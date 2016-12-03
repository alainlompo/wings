%%
%%  wings_bool.erl --
%%
%%     This module implements boolean commands for Wings objects.
%%
%%  Copyright (c) 2016 Dan Gudmundsson
%%
%%  See the file "license.terms" for information on usage and redistribution
%%  of this file, and for a DISCLAIMER OF ALL WARRANTIES.
%%
%%     $Id$
%%

-module(wings_bool).
-export([add/1]).

-include("wings.hrl").

-compile(export_all).
-define(EPSILON, 1.0e-15).

add(#st{shapes=Sh0}=St0) ->
    MapBvh = wings_sel:fold(fun make_bvh/3, [], St0),
    IntScts = find_intersects(MapBvh, MapBvh, []),
    MFs = lists:append([MFL || #{fs:=MFL} <- IntScts]),
    Sel0 = sofs:relation(MFs, [{id,data}]),
    Sel1 = sofs:relation_to_family(Sel0),
    Sel2 = sofs:to_external(Sel1),
    Sel = [{Id,gb_sets:from_list(L)} || {Id,L} <- Sel2],
    % ?dbg("~p~n", [Sel2]),
    Sh = lists:foldl(fun(#{we:=Wes}, Sh) ->
                             case Wes of
                                 We=#we{id=Id} ->
                                     gb_trees:update(Id, We, Sh);
                                 {We1=#we{id=Id1},We2=#we{id=Id2}} ->
                                     Sh2 = gb_trees:update(Id1, We1, Sh),
                                     gb_trees:update(Id2, We2, Sh2)
                             end
                     end, Sh0, IntScts),
    wings_sel:set(face, Sel, St0#st{shapes=Sh}).

find_intersects([Head|Tail], [_|_] = Alts, Acc) ->
    case find_intersect(Head, Alts) of
	false ->
	    find_intersects(Tail,Alts, Acc);
	{H1,Merge} ->
	    %% ?dbg("~p,~p => ~p~n",
	    %% 	      [maps:get(id, Head), maps:get(id, H1), maps:get(fs,Merge)]),
	    NewTail = [Merge|remove(H1, Head, Tail)],
	    NewAlts = [Merge|remove(H1, Head, Alts)],
	    find_intersects(NewTail, NewAlts, [Merge|remove(Head,Acc)])
    end;
find_intersects(_, _, Acc) -> lists:reverse(Acc).

find_intersect(#{id:=Id}=Head, [#{id:=Id}|Rest]) ->
    find_intersect(Head, Rest);
find_intersect(#{bvh:=B1}=Head, [#{bvh:=B2}=H1|Rest]) ->
    case e3d_bvh:intersect(B1, B2) of
	[] ->  find_intersect(Head,Rest);
	EdgeInfo -> {H1, merge(EdgeInfo, Head, H1)}
    end;
find_intersect(_Head, []) ->
    false.

merge(EdgeInfo, #{id:=Id1,fs:=Fs1,we:=We1}=I1, #{id:=Id2,fs:=Fs2,we:=We2}=I2) ->
    ReEI0 = [remap(Edge, I1, I2) || Edge <- EdgeInfo],
    {Vmap, ReEI} = make_vmap(ReEI0, e3d_kd3:empty(), 0, []),
    Tab = make_lookup_table(ReEI),
    Loops0 = build_vtx_loops(Tab, []),
    L10 = [split_loop(Loop, Id1) || Loop <- Loops0],
    L20 = [split_loop(Loop, Id2) || Loop <- Loops0],
    Loops = [filter_tri_edges(Loop, We1, We2) || Loop <- lists:zip(L10,L20)],
    {L1,L2} = lists:unzip(Loops),
    We1N = make_verts(L1, Vmap, We1),
    We2N = make_verts(L2, Vmap, We2),
    MFs = lists:flatten([[MF1,MF2] || #{mf1:=MF1,other:=MF2} <- ReEI]),
    I1#{id:=min(Id1,Id2),fs:=Fs1++Fs2++MFs, we:={We1N,We2N}}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
make_verts(Loops, Vmap0, We0) ->
    All = lists:append(Loops),
    SE = [SP || #{op:=split_edge}=SP <- All],
    {Vmap, We1} = cut_edges(SE, Vmap0, We0),
    EL = fun(Loop, We) -> make_edge_loop(Loop, Vmap, We) end,
    We = lists:foldl(EL, We1, Loops),
    ok = wings_we_util:validate(We),
    We.

cut_edges(SE, Vmap, We0) ->
    WiEs = [{E,Vn} || #{op:=split_edge, e:=E, v:=Vn} <- SE],
    ECuts = sofs:to_external(sofs:relation_to_family(sofs:relation(WiEs, [{edge,vn}]))),
    lists:foldl(fun cut_edge/2, {Vmap, We0}, ECuts).

cut_edge({Edge, [V]}, {Vmap, We0}) ->
    Pos = array:get(V, Vmap),
    {We, NewV} = wings_edge:fast_cut(Edge, Pos, We0),
    {array:set(V, NewV, Vmap), We};
cut_edge({Edge, Vs}, {Vmap0, #we{es=Etab}=We0}) ->
    #edge{vs=VS,ve=VE} = array:get(Edge, Etab),
    Pt1 = wings_vertex:pos(VS,We0),
    Pt2 = wings_vertex:pos(VE,We0),
    [{_,Pt3},{_,Pt4}|_] = VsPos0 = [{V,array:get(V, Vmap0)} || V <- Vs],
    VsPos = case e3d_vec:dot(e3d_vec:sub(Pt2, Pt1), e3d_vec:sub(Pt4, Pt3)) > 0 of
                true -> VsPos0;
                false -> lists:reverse(VsPos0)
            end,
    {We,_,Vmap} = lists:foldl(fun({V,Pos}, {WE, E, Vm}) ->
                                      {We, New} = wings_edge:fast_cut(E, Pos, WE),
                                      {We, New, array:set(V, New, Vm)}
                              end, {We0, Edge, Vmap0}, VsPos),
    {Vmap, We}.

make_edge_loop([#{op:=split_edge}=F|_]=Loop, Vmap, We) ->
    ?dbg("Loop ~p~n",[Loop]),
    make_edge_loop_1(Loop, F, Vmap, We);
make_edge_loop(Loop, Vmap, We) ->
    case lists:splitwith(fun(#{op:=Op}) -> Op =:= split_face end, Loop) of
        {FSs, []} -> split_face(FSs, Vmap, We);
        {FSs, Edges} -> make_edge_loop(Edges++FSs, Vmap, We)
    end.

make_edge_loop_1([#{op:=split_edge,v:=V1}|[#{op:=split_edge,v:=V2}|_]=Rest], Last, Vmap, We0) ->
    {We, _New} = connect_verts(V1,V2,Vmap, We0),
    make_edge_loop_1(Rest, Last, Vmap, We);
make_edge_loop_1([#{op:=split_edge,v:=V1}],#{op:=split_edge,v:=V2}, Vmap, We0) ->
    {We, _New} = connect_verts(V1,V2,Vmap, We0),
    We;
make_edge_loop_1([#{op:=split_edge,v:=V1}|Splits], Last, Vmap, We0) ->
    case lists:splitwith(fun(#{op:=Op}) -> Op =:= split_face end, Splits) of
        {FSs, []} ->
            #{op:=split_edge,v:=V2} = Last,
            Face = pick_face(FSs,undefined),
            {We1, Edge} = connect_verts(V1,V2,Face,Vmap,We0),
            ok = wings_we_util:validate(We1),
            We = make_face_vs(FSs, array:get(V2, Vmap), Edge, Vmap, We1),
            We;
        {FSs, [#{op:=split_edge,v:=V2}|_]=Rest} ->
            Face = pick_face(FSs,undefined),
            {We1, Edge} = connect_verts(V1,V2,Face,Vmap,We0),
            ok = wings_we_util:validate(We1),
            We = make_face_vs(FSs, array:get(V2, Vmap), Edge, Vmap, We1),
            make_edge_loop_1(Rest, Last, Vmap, We)
    end.

pick_face([#{f:=F}|Ss], undefined) ->
    pick_face(Ss, F);
pick_face([#{f:=F}|Ss], F) ->
    pick_face(Ss, F);
pick_face([], F) -> F.

connect_verts(V1,V2,Vmap, We) ->
    WeV1 = array:get(V1, Vmap),
    WeV2 = array:get(V2, Vmap),
    true = is_integer(WeV1), true = is_integer(WeV2), %% Assert
    [Face] = [Face || {Face, [_,_]} <- wings_vertex:per_face([WeV1,WeV2],We)],
    wings_vertex:force_connect(WeV1,WeV2,Face,We).

connect_verts(V1,V2,Face,Vmap,We) ->
    WeV1 = array:get(V1, Vmap),
    WeV2 = array:get(V2, Vmap),
    case wings_vertex:edge_through(WeV1,WeV2,Face,We) of
        none -> wings_vertex:force_connect(WeV1,WeV2,Face,We);
        Edge -> {We, Edge}
    end.

make_face_vs([_]=Ss, _Vs, Edge, Vmap, We) ->
    make_face_vs_1(Ss, Edge, Vmap, We);
make_face_vs(Ss, Vs, Edge, Vmap, #we{es=Etab}=We) ->
    case array:get(Edge, Etab) of
        #edge{vs=Vs} -> make_face_vs_1(lists:reverse(Ss), Edge, Vmap, We);
        #edge{ve=Vs} -> make_face_vs_1(Ss, Edge, Vmap, We)
    end.

make_face_vs_1([#{op:=split_face,v:=V}|Ss], Edge, Vmap, We0) ->
    Pos = array:get(V, Vmap),
    {We, New} = wings_edge:fast_cut(Edge, Pos, We0),
    make_face_vs_1(Ss, New, Vmap, We);
make_face_vs_1([], _, _, We) ->
    We.

split_face(Fs, Vmap, We) ->
    Face = pick_face(Fs, undefined),
    true = length(Fs) > 2, %% Otherwise something is wrong
    FPos = wings_face:vertex_positions(Face, We),
    FVs = wings_face:vertex_ccw(Face, We),
    KD3 = e3d_kd3:from_list(lists:zip(FPos, FVs)),
    lists:mapfoldl(fun(#{v:=Vi}, Tree) ->
                           e3d_kd3:take_nearest(array:get(Vi, Vmap), Tree)
                   end, KD3, Fs),
    We.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
filter_tri_edges({L10,L20}, We1, We2) ->
    Replace = fun(#{op:=split_edge, f:=Face,e:={A,B}}=V, We) ->
                      V#{e:=wings_vertex:edge_through(A,B,Face,We)};
                 (V,_) -> V
              end,
    L1 = [Replace(E,We1) || E <- L10],
    L2 = [Replace(E,We2) || E <- L20],
    Loop = lists:zip(L1,L2),
    lists:unzip(filter_tri_edges(Loop)).

filter_tri_edges([{#{op:=split_edge,e:=none},#{op:=split_edge, e:=none}}|Vs]) ->
    filter_tri_edges(Vs);
filter_tri_edges([{#{op:=split_edge,e:=none}=V1,#{op:=Op}=V2}|Vs]) ->
    case Op of
        split_face -> filter_tri_edges(Vs);
        split_edge -> [{edge_to_face(V1), V2}|filter_tri_edges(Vs)]
    end;
filter_tri_edges([{#{op:=Op}=V1,#{op:=split_edge,e:=none}=V2}|Vs]) ->
    case Op of
        split_face -> filter_tri_edges(Vs);
        split_edge -> [{V1,edge_to_face(V2)}|filter_tri_edges(Vs)]
    end;
filter_tri_edges([V|Vs]) ->
    [V|filter_tri_edges(Vs)];
filter_tri_edges([]) -> [].

edge_to_face(#{op:=split_edge, o:=O, f:=F, v:=V}) ->
    #{op=>split_face, o=>O, f=>F, v=>V}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% We need to build the cycle our selfves since the edges may not be directed
%% in the correct direction. Also the V is new Vs on edges and there maybe
%% several new V on the same wings edge.

build_vtx_loops(G, _Acc) ->
    Comps = digraph_utils:components(G),
    %?dbg("Cs: ~p: ~p~n",[G, Comps]),
    [build_vtx_loop(C, G) || C <- Comps].

build_vtx_loop([V|_Vs], G) ->
    %% ?dbg("v: ~p~n  ", [V]),
    %% [io:format("~p ", [digraph:edge(G, E)]) || E <- digraph:edges(G,V)],
    %% io:nl(),
    [Edge|_] = case digraph:out_edges(G,V) of
                 [] -> digraph:in_edges(G,V);
                 Out -> Out
             end,
    case digraph:edge(G, Edge) of
        {_, _, _, #{p1:={_,V}, p2:={_,Next}}=Ei} -> Next;
        {_, _, _, #{p2:={_,V}, p1:={_,Next}}=Ei} -> Next
    end,
    digraph:del_edge(G, Edge),
    build_vtx_loop(Next, V, G, [Ei,V]).

build_vtx_loop(Start, Start, _G, Acc) ->
    Acc;
build_vtx_loop(V0, Start, G, Acc) ->
    Es = [digraph:edge(G, E) || E <- digraph:edges(G, V0)],
    %% ?dbg("~p => ~p ~n",[V0, Es]),
    {Edge, Next, Ei} = pick_edge(Es, V0, undefined),
    digraph:del_edge(G, Edge),
    build_vtx_loop(Next, Start, G, [Ei,V0|Acc]).

pick_edge([{E,V,V,Ei}|_], V, _Best) ->
    {E, V, Ei}; %% Self cyclic pick first
pick_edge([{E,V,N,Ei}|R], V, _Best) ->
    pick_edge(R, V, {E,N,Ei});
pick_edge([{E,N,V,Ei}|R], V, _Best) ->
    pick_edge(R, V, {E,N,Ei});
pick_edge([], _, Best) -> Best.

split_loop([Last|Loop], Id1) ->
    split_loop(Loop, Last, Id1, []).

split_loop([V1,E|Loop], Last, Id, Acc) when is_integer(V1) ->
    Vertex = vertex_info(E, V1, Id),
    split_loop(Loop, Last, Id, [Vertex|Acc]);
split_loop([V1], E, Id, Acc) ->
    Vertex = vertex_info(E, V1, Id),
    lists:reverse([Vertex|Acc]).

vertex_info(#{mf1:={O1,F1}, mf2:={O2,F2}, other:={O3,F3}, p1:={{_, Edge},V0}}, V0, Id) ->
    if O1 =:= Id -> #{op=>split_edge, o=>O1, f=>F1, e=>Edge, v=>V0};
       O2 =:= Id -> #{op=>split_face, o=>O2, f=>F2, v=>V0};
       O3 =:= Id -> #{op=>split_face, o=>O3, f=>F3, v=>V0}
    end;
vertex_info(#{mf2:={O1,F1}, mf1:={O2,F2}, other:={O3,F3}, p2:={{_, Edge},V0}}, V0, Id) ->
    if O1 =:= Id -> #{op=>split_edge, o=>O1, f=>F1, e=>Edge, v=>V0};
       O2 =:= Id -> #{op=>split_face, o=>O2, f=>F2, v=>V0};
       O3 =:= Id -> #{op=>split_face, o=>O3, f=>F3, v=>V0}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

make_bvh(_, #we{id=Id, fs=Fs0}=We0, Bvhs) ->
    Fs = gb_trees:keys(Fs0),
    {Vtab,Ts} = triangles(Fs, We0),
    Get = fun({verts, Face}) -> element(1, array:get(Face, Ts));
	     (verts) -> Vtab;
	     (meshId) -> Id
	  end,
    Bvh = e3d_bvh:init([{array:size(Ts), Get}]),
    [#{id=>Id,map=>Ts,bvh=>Bvh,fs=>[],we=>We0}|Bvhs].

%% BUGBUG: Should we add the We's vertexes here!!
%% That way we can merge new verts with original Vs directly
make_vmap([#{p1:=P10, p2:=P20}=E|R], T0, N0, Acc) ->
    {P1, N1, T1} = vmap(P10, N0, T0),
    {P2, N2, T2} = vmap(P20, N1, T1),
    make_vmap(R, T2, N2, [E#{p1:=P1,p2:=P2}|Acc]);
make_vmap([], T, _, Acc) ->
    PosList = [Pos || {Pos,_} <- lists:keysort(2,e3d_kd3:to_list(T))],
    {array:from_list(PosList), Acc}.

vmap({Where, Pos}, N, Tree) ->
    case e3d_kd3:is_empty(Tree) of
        true -> {{Where, N}, N+1, e3d_kd3:enter(Pos, N, Tree)};
        false ->
            {P1, V1} = e3d_kd3:nearest(Pos, Tree),
            case e3d_vec:dist_sqr(Pos, P1) < ?EPSILON of
                true  -> {{Where, V1}, N, Tree};
                false -> {{Where, N}, N+1, e3d_kd3:enter(Pos, N, Tree)}
            end
    end.

make_lookup_table(Edges) ->
    G = digraph:new(),
    Add = fun(#{p1:={_,P1},p2:={_,P2}}=EI) ->
                  digraph:add_vertex(G, P1),
                  digraph:add_vertex(G, P2),
                  digraph:add_edge(G, P1, P2, EI)
          end,
    _ = [Add(EI) || EI <- Edges],
    G.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove(#{id:=Id}, List) ->
    Map = mapsfind(Id, id, List),
    lists:delete(Map, List).

remove(H1, H2, List) ->
    remove(H1, remove(H2, List)).

remap(#{mf1:=MF10,mf2:=MF20,p1:={Pos1,E11,E12}, p2:= {Pos2, E21, E22}, other:=Other},
      #{id:=Id1,map:=M1}, #{id:=Id2,map:=M2}) ->
    MF1 = remap_1(MF10, Id1, M1, Id2, M2),
    MF2 = remap_1(MF20, Id1, M1, Id2, M2),
    Oth = remap_1(Other, Id1, M1, Id2, M2),
    EId1 = {element(1,MF1), order(E11,E12)},
    EId2 = {element(1,MF2), order(E21,E22)},
    case Id1 < Id2 of
        true  -> #{mf1=>MF1, mf2=>MF2, p1=>{EId1, Pos1}, p2=>{EId2, Pos2}, other=>Oth};
        false -> #{mf1=>MF2, mf2=>MF1, p1=>{EId2, Pos2}, p2=>{EId1, Pos1}, other=>Oth}
    end.

remap_1({Id, TriFace}, Id, M1, _Id2, _M2) ->
    {_, Face} = array:get(TriFace, M1),
    {Id, Face};
remap_1({Id, TriFace}, _Id, _M1, Id, M2) ->
    {_, Face} = array:get(TriFace, M2),
    {Id, Face}.

order(V1, V2) when V1 < V2 ->  {V1,V2};
order(V2, V1) -> {V1,V2}.

%% Use wings_util:mapsfind
mapsfind(Value, Key, [H|T]) ->
    case H of
	#{Key:=Value} -> H;
	_ -> mapsfind(Value, Key, T)
    end;
mapsfind(_, _, []) -> false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

triangles(Fs, We0) ->
    {#we{vp=Vtab}, Ts} = lists:foldl(fun triangle/2, {We0,[]}, Fs),
    {Vtab, array:from_list(Ts)}.

triangle(Face, {We, Acc}) ->
    Vs = wings_face:vertices_ccw(Face, We),
    case length(Vs) of
	3 -> {We, [{list_to_tuple(Vs), Face}|Acc]};
	4 -> tri_quad(Vs, We, Face, Acc);
	_ -> tri_poly(Vs, We, Face, Acc)
    end.

tri_quad([Ai,Bi,Ci,Di] = Vs, #we{vp=Vtab}=We, Face, Acc) ->
    [A,B,C,D] = VsPos = [array:get(V, Vtab) || V <- Vs],
    N = e3d_vec:normal(VsPos),
    case wings_tesselation:is_good_triangulation(N, A, B, C, D) of
	true  -> {We, [{{Ai,Bi,Ci}, Face}, {{Ai,Ci,Di}, Face}|Acc]};
	false -> {We, [{{Ai,Bi,Di}, Face}, {{Bi,Ci,Di}, Face}|Acc]}
    end.

tri_poly(Vs, #we{vp=Vtab}=We, Face, Acc0) ->
    VsPos = [array:get(V, Vtab) || V <- Vs],
    N = e3d_vec:normal(VsPos),
    {Fs0, Ps0} = wings_gl:triangulate(N, VsPos),
    Index = array:size(Vtab),
    {TessVtab, Is} = renumber_and_add_vs(Ps0, Vs, Index, Vtab, []),
    Fs = lists:foldl(fun({A,B,C}, Acc) ->
			     F = {element(A,Is), element(B, Is), element(C,Is)},
			     [{F, Face}|Acc]
		     end, Acc0, Fs0),
    {We#we{vp=TessVtab}, Fs}.

renumber_and_add_vs([_|Ps], [V|Vs], Index, Vtab, Acc) ->
    renumber_and_add_vs(Ps, Vs, Index, Vtab, [V|Acc]);
renumber_and_add_vs([Pos|Ps], [], Index, Vtab0, Acc) ->
    Vtab = array:add(Index, Pos, Vtab0),
    renumber_and_add_vs(Ps, [], Index+1, Vtab, [Index|Acc]);
renumber_and_add_vs([], [], _, Vtab, Vs) ->
    {Vtab, list_to_tuple(lists:reverse(Vs))}.

