-module(muhash).

-compile([debug_info, nowarn_export_all, export_all, nowarn_unused_function, nowarn_unused_type]).

-import(musem, [var_name/0, ast/0, fresh_rec_var/0, any/0, empty/0, unfold_toplevel_recursive_types/1]).
-type ast() :: musem:ast().
-type var_name() :: musem:var_name().

%  Given an epxression that consists of the following terms
% 
%  t = 
%   flag
%   | {t, t} 
%   | !t 
%   | t U t 
%   | alpha 
%   | mu alpha . t
% 
%  First, we want to hash terms to the same value module mu-equivalence.
%  Here, mu-equivalence means terms equivalent up to renaming of the recursion variables.
%  This means we need to implement mu-equivalence checking of ast() terms.
%
%  The following is an implementation of the paper
%  "Hashing Modulo Alpha-Equivalence (PLDI21)".
%
%  The summary of an "ast()" term is described by the shape of the term without variables
%  and a variable map filling the shape with proper variable names.


% this bit corresponds to expression part of esummary
 
% -record(structure, {struct = #{}, position = #{}, hash = 0}).
-record(var_map, {entries = #{}, existing_hash = 0}).

-type var_map() :: #var_map{}.

-type hash() :: integer().

-type structure() :: hash().

% esummary is actually a tuple or record or map
% esummary consists of structure which is a hash, variable map and combined hash
-type esummary() :: {structure(), var_map(), hash()}.

-record(esummary, {structure = 0, var_map = #var_map{}, mu_hash = 0}).

% weak hash combiner similar to C++ boost::hash_combine.
-spec hash(_) -> hash().
hash(A) ->
  erlang:phash2(A).


-spec hash_combine(_,_) -> hash().
hash_combine(A, B) ->
    CombineWithSeed = fun(Seed, X) -> 
        Seed bxor (X + 2654435769 + (Seed bsl 6) + (Seed bsr 2))
    end,
    CombineWithSeed(CombineWithSeed(A, B),0).


-spec then_hash(hash(), _) -> hash().
then_hash(XHash, Y) ->
     hash_combine(XHash, hash(Y)).


-spec entry_hash(var_name(), hash()) -> hash().
entry_hash(Key,Pos) -> then_hash(hash(Key),Pos).

-spec singleton_vm(var_name(), hash()) ->var_map().
singleton_vm(Key, Pos) ->
    #var_map{entries = #{Key => Pos}, existing_hash = entry_hash(Key, Pos)}.

-spec hash_vm(var_map()) -> hash().
hash_vm(#var_map{existing_hash = H}) ->
    H.

-spec remove_from_vm(var_name(), var_map()) -> {var_map(), _}.
remove_from_vm(Key, #var_map{entries = Entries, existing_hash = OldHash} = VM) ->
    case maps:find(Key, Entries) of
        {ok, Pt} ->
            NewEntries = maps:remove(Key, Entries),
            NewHash = OldHash bxor entry_hash(Key, Pt),
            {#var_map{entries = NewEntries, existing_hash = NewHash}, {ok, Pt}};
        error ->
            {VM, undefined}
    end.

-spec alter_vm(_, var_name(), var_map()) -> var_map().
alter_vm(F, Key, #var_map{entries=Entries, existing_hash=OldHash}) ->
    {NewHash, NewMap} = maps:fold(fun(K, V, {AccHash, AccMap}) ->
        NewPos = F(case maps:find(K, AccMap) of
            {ok, OldPos} -> OldPos;
            error -> error
        end),
        NewHash = (AccHash bxor entry_hash(K, V)) bxor entry_hash(K, NewPos),
        {NewHash, maps:put(K, NewPos, AccMap)}
    end, {OldHash, Entries}, Entries),
    #var_map{entries=NewMap, existing_hash=NewHash}.


-spec size_vm(var_map()) -> integer().
size_vm(#var_map{entries=M}) -> 
  maps:size(M).

-spec to_list_vm(var_map()) -> list().
to_list_vm(#var_map{entries=M}) -> 
  maps:to_list(M).

-spec mk_svar() -> hash().
mk_svar() ->
    hash("Svar").

-spec mk_herepl() -> hash().
mk_herepl() ->
    hash("HerePL").

% below are hash combinators
-spec mk_slam(_,_,_) -> hash().
mk_slam(A, B, C) ->
    then_hash(then_hash(then_hash(hash("SLam"), A), B), C).

-spec mk_join_pl(_,_,_) -> hash().
mk_join_pl(A, B, C) -> 
  then_hash(then_hash(then_hash(hash("JoinPL"), A), B), C).

-spec mk_s_app(_,_,_,_) -> hash().
mk_s_app(A, B, C, D) -> 
  then_hash(then_hash(then_hash(then_hash(hash("SApp"), A), B), C), D).


-spec summarize(ast()) -> esummary().
summarize({recursion_variable, Var}) -> 
  Structure = mk_svar(), 
  PositionMap = singleton_vm(Var, mk_herepl()),
  #esummary{structure = Structure, var_map = PositionMap, mu_hash = then_hash(hash(Structure), hash_vm(PositionMap))};
summarize({mu, {recursion_variable, Var}, InnerTy}) ->
  #esummary{structure = StrBody, var_map = MapBody, mu_hash = E} = summarize(InnerTy),
  {EMap, XPos} = remove_from_vm(Var, MapBody),
  Structure = mk_slam(StrBody, XPos, StrBody),
  PositionMap = EMap,
  #esummary{structure = Structure, var_map = PositionMap, mu_hash = then_hash(hash(Structure), hash_vm(PositionMap))};
summarize({flag}) ->
  Structure = mk_svar(),
  PositionMap = #var_map{},
  #esummary{structure = Structure, var_map = PositionMap, mu_hash = then_hash(hash(Structure), hash_vm(PositionMap))};
summarize({union, Ty1, Ty2}) ->
  #esummary{structure = Str1, var_map = Map1, mu_hash = E1} = summarize(Ty1),
  #esummary{structure = Str2, var_map = Map2, mu_hash = E2} = summarize(Ty2),
  AppDepth = hash_combine(Str1, Str2),
  Tag = AppDepth,
  LeftBigger = size_vm(Map1) >= size_vm(Map2),
  {BigVM, SmallVM} = if LeftBigger -> {Map1, Map2}; true -> {Map2, Map1} end,
  PositionMap = lists:foldl(fun({V, P}, AccVM) ->
    alter_vm(fun(MP) -> mk_join_pl(Tag, MP, P) end, V, AccVM)
    end, BigVM, to_list_vm(SmallVM)),
  Structure = mk_s_app(Tag, hash(LeftBigger), Str1, Str2),
  #esummary{structure = Structure, var_map = PositionMap, mu_hash = then_hash(hash(Structure), hash_vm(PositionMap))};
summarize({product, Ty1, Ty2}) ->
  #esummary{structure = Str1, var_map = Map1, mu_hash = E1} = summarize(Ty1),
  #esummary{structure = Str2, var_map = Map2, mu_hash = E2} = summarize(Ty2),
  AppDepth = hash_combine(Str1, Str2),
  Tag = AppDepth,
  LeftBigger = size_vm(Map1) >= size_vm(Map2),
  {BigVM, SmallVM} = if LeftBigger -> {Map1, Map2}; true -> {Map2, Map1} end,
  PositionMap = lists:foldl(fun({V, P}, AccVM) ->
    alter_vm(fun(MP) -> mk_join_pl(Tag, MP, P) end, V, AccVM)
    end, BigVM, to_list_vm(SmallVM)),
  Structure = mk_s_app(Tag, hash(LeftBigger), Str1, Str2),
  #esummary{structure = Structure, var_map = PositionMap, mu_hash = then_hash(hash(Structure), hash_vm(PositionMap))};
summarize({negation, InnerTy}) ->
  #esummary{structure = StrBody, var_map = MapBody, mu_hash = E} = summarize(InnerTy),
  PositionMap = MapBody,
  Structure = mk_slam(StrBody, PositionMap, StrBody),
  #esummary{structure = Structure, var_map = PositionMap, mu_hash = then_hash(hash(Structure), hash_vm(PositionMap))}.

% final hash code from summarize
-spec mu_hash(esummary()) -> hash().
mu_hash(Ty) ->
  #esummary{mu_hash = H} = summarize(Ty),
  H.

%  Further, there is a method to reconstruct an ast() term from a summary, 
%  up to mu-renaming of the recursion variables. 
-spec rebuild(esummary()) -> musem:ast().
rebuild(_) -> error(not_implemented).

%  We can now define a predicate for mu-equivalence testing
%  which compares the summaries of the two given types
-spec is_mu_equivalent(ast(), ast()) -> boolean().
is_mu_equivalent(Ty1, Ty2) -> 
  summarize(Ty1) =:= summarize(Ty2).

-spec mu_equivalence_test() -> ok.
mu_equivalence_test() ->
  true = is_mu_equivalent(any(), any()),
  true = is_mu_equivalent(empty(), empty()),
  false = is_mu_equivalent(empty(), any()),

  % equivalence modulo mu-renaming
  Var = {recursion_variable, any2},
  AnyMuEquivalent = {mu, Var, {union, {flag}, {product, Var, Var}}},
  true = is_mu_equivalent(any(), AnyMuEquivalent),

  % following tests are for better understanding and clarity of mu-equivalence
  % if there is no recursion binder then the variables, union and products
  % are not mu-equivalent i.e. they have different esummary

  Var1 = {recursion_variable, any},

  false = is_mu_equivalent(Var1, Var),

  false = is_mu_equivalent({union, Var1, Var1}, {union, Var, Var}),
  
  false = is_mu_equivalent({product, Var1, Var1}, {product, Var, Var}),

  % when recursion binder is involved
  true = is_mu_equivalent({mu, Var1, {flag}}, {mu, Var, {flag}}),

  Mu1 = {mu, Var1, {product, Var1, Var1}},
  Mu2 = {mu, Var,  {product, Var,  Var}},

  true = is_mu_equivalent(Mu1, Mu2),

  Mu3 = {mu, Var1, {union, {flag}, Var1}},
  Mu4 = {mu, Var,  {union, {flag},  Var}},

  true = is_mu_equivalent(Mu3, Mu4),

  % equivalence modulo unfolding
  AnyUnfoldedOnce = {union, {flag}, {product, any(), any()}},
  false = is_mu_equivalent(any(), AnyUnfoldedOnce),
  
  ok.
