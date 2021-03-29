

(**
This file contains the nullable finder function.
*)
Require Import List.
Import ListNotations.
Require Import Wf_nat.
Require Import Earley.datastructures.
Require Import Earley.grammarDep.


Section grammarcontext.
(**
N and T are the set of terminals and nonterminals.
They should be finite, but for terminals we do not enforce this,
as the grammar can only contain finite number of finite length
rules
*)
Variable N T:Type.

(**
We sometimes need to iterate over all
the nonterminals, so the set of nonterminals
is also included in an iterable datatype
(list in this implementation).
*)
Variable ntSet: list N.
Variable ntSetComplete: forall n:N, n ∊ ntSet.


(**
Terminals and nonterminals must have decidable equality.
*)
Variable nEq: forall (n1 n2: N), {n1 = n2} + {n1 <> n2}.
Variable tEq: forall (t1 t2: T), {t1 = t2} + {t1 <> t2}.

(**The grammar that we work on.*)
Variable G:grammar N T.

Instance grammarruleInOpClass: InOpClass (rule N T) (grammar N T):=
  fun r g => In r (grammarGetRules g).

Variable grammarruleInOpDecClass: InOpDecClass (rule N T) (grammar N T) grammarruleInOpClass.

Existing Instance grammarruleInOpDecClass.

(**
Various dictionary implementations.
*)
Variable (nDm:MultiDictionary N).
Variable (nDd:DependentDefaultDictionary N).

(**
Relations for the correctness proof
*)

Definition isNullable n:= inhabited (forall i k, parseTreeDep N T G i k k n).

(**
isDescendantTree is (equivalent to) True if the nonterminal
appears somwhere in the parsetree, except at the root.
*)
(*
Inductive isDescendantTree {i}: forall {bpos epos n}
  (m:N) (pt:parseTreeDep N T G i bpos epos n), Prop:=
  | idtNode n m rl bpos poss (pf: parseForestDep N T G i bpos poss rl)
  pI (pF: isDescendantForest m pf)
  : isDescendantTree m (ptNode G i n rl bpos poss pf pI)
with
isDescendantForest {i}: forall {bpos poss rl}
  (m:N) (pf: parseForestDep N T G i bpos poss rl),Prop :=
  | idfHead m b1 e1 pt poss (rl:list (N + T)) pf: isDescendantForest m (pfSub N T G i b1 e1 m pt poss rl pf)
  | idfNext m b1 e1 n1 pt poss (rl:list (N + T)) pf (pI:isDescendantTree m pt): isDescendantForest m (pfSub N T G i b1 e1 n1 pt poss rl pf)
  | idfTail1 m b1 e1 n1 pt poss (rl:list (N + T)) pf (pI:isDescendantForest m pf): isDescendantForest m (pfSub N T G i b1 e1 n1 pt poss rl pf)
  | idfTail2 m b1 c poss (rl:list (N + T)) pf (pI:isDescendantForest m pf) pAt: isDescendantForest m (pfTrm N T G i b1 c (b1+1) poss rl pf eq_refl pAt).

Instance isDescendantTreeInOpClass {i bpos epos n}:
  InOpClass N (parseTreeDep N T G i bpos epos n):=
isDescendantTree.

Definition hasEmptyRule: N->Prop:=
fun n => ruleConstr n [] ∊ G.


Lemma nullTreeHasEmptyRule:
    forall i k n (pt:parseTreeDep N T G i k k n),
    hasEmptyRule n \/
    (exists m, m ∊ pt /\ hasEmptyRule m).
Admitted.
*)

(**
First we create a dictionary of all rules indexed by the
nonterminals of the right hand side.
There is one little bug, if symbols occur
multiple times in the same rule (e.g. CC <- BB BB), it is inserted
more than once.
*)  
Definition createRHSdic_aux
  (dic : mdictionary N {r:rule N T |  r ∊ G})
  (r : {r:rule N T | r ∊ G }):
  mdictionary N {r:rule N T | r ∊ G }
:=
let '(exist _ hd pHh):= r in
foldl (fun dic hd =>
        match hd with
          | inl n => minsert n r dic
          | inr t => dic
        end)
      dic
      (rhs hd).

Definition createRHSdic: mdictionary N {r:rule N T | r ∊ G } :=
foldl createRHSdic_aux
      memptyDictionary
      (listToMembershipProofList (grammarGetRules G)).

(**
Type aliases for the dependent dictionary.
*)
Definition parseTreeDicFun:=
    fun n:N => Maybe (forall i k, parseTreeDep N T G i k k n).
Definition parseTreeDic:=dddictionary N (parseTreeDicFun).


(** We look at each symbol in the rhs of the rule, check if they are
nullable. If all of them are nullable, we return the parseforest
that correspond to the input symbols
and if any of them is not nullable, we return Nothing *)
Fixpoint rule_loop_body_aux
    (a:list (N+T)) (nullabledic: parseTreeDic) {struct a}:
    Maybe (forall i k, parseForestDep N T G i (fmap (fun _ => k) a) k a).
refine(
  match a as a0
  return a = a0 -> Maybe (forall i k, parseForestDep N T G i
                     (fmap (fun _ =>  k) a0) k a0)
  with
    | nil => fun Heqa => Just (fun i k => pfNil _ _ _ _ _)
    | inl hdn :: tl => fun Heqa => match (ddlookup hdn nullabledic) with
                    | Nothing => Nothing
                    | Just pt =>
                    match rule_loop_body_aux tl nullabledic with
                      | Nothing => Nothing
                      | Just pf =>
                         Just (fun i k => pfSub N T G _ _ _ hdn (pt i k) _ _ _ (pf i k) _)
                    end
                   end
    | inr hdt :: tl => fun Heqa => Nothing
             (** The next symbol of the rhs is a terminal *)
  end eq_refl
).
destruct tl; reflexivity.
Defined.



(**The running state of the algorithm*)
Inductive nState
  (nyfl:list N) (*List of not yet processed symbols.
      We need it as a parameter, because it is the decreasing
      argument of symbol_loop, and must be passed unmodified
      through the rule_loop.*)
  := nStateConstr
  (s:ustack N) (*Unique stack of symbols.*)
  (dic:parseTreeDic) (*Dictionary of the nullable state of symbols.*)
  (*Invariants of the state: the not yet processed symbols
     are exactly those, that are either on the stack, or (exclusive or) not declared nullable in the dictionary.*)
  (pI: forall n, (n ∊ s \/ ddlookup n dic = Nothing) -> n ∊ nyfl)
  (pIr: forall n, n ∊ nyfl ->
         (n ∊ s /\ ~ ddlookup n dic = Nothing \/
          ddlookup n dic = Nothing /\ ~ n ∊ s))
  (*The actually nullable symbols that are not yet in the stack
     must have at least one descendant on the stack.*)
  (*pDes: forall n, isNullable n -> ddlookup n dic = Nothing ->
    (forall i k, 
       exists (t:parseTreeDep N T G i k k n) m, m ∊ s /\ m ∊ t)*) 
  : nState nyfl.



Definition initializeState: nState ntSet.
refine(
foldl
  (fun '(nStateConstr _ s dic pI pIr)
       '(exist _ ru rI) =>
    match ddlookup (lhs ru) dic as s0
    return (ddlookup (lhs ru) dic)=s0 -> _ with
      | Nothing => fun Heqs =>
           match rhs ru as r0 return (rhs ru)=r0 -> _ with
             | nil => fun Heqr => (*Empty rule*)
                 let '(exist _ s1 (conj pP1 pP2)):=
                   upush_in (lhs ru) s ?[pNI] in
                 nStateConstr ntSet
                   s1
                   (ddinsert (lhs ru)
                     (Just (fun i k => ptNode G i (lhs ru)
                             nil k nil k
                             (pfNil N T G i k) ?[rI1] eq_refl))
                     dic)
                   ?[pI1] ?[pIr1]
             | _ :: _ => fun Heqr => (*Nonempty, no change*)
                 nStateConstr ntSet s dic pI pIr
           end eq_refl
      | Just _ => fun Heqs => (*Already on the stack*)
          nStateConstr ntSet s dic pI pIr
    end eq_refl)
  (nStateConstr ntSet uemptystack
    (@ddemptyDictionary N nDd parseTreeDicFun (fun n=> Nothing))
    ?[pI2] ?[pIr2])
  (listToMembershipProofList (grammarGetRules G))
).
[pNI]:{
  pose proof (ntSetComplete).
  firstorder.
}
[pI1]:{ firstorder. }
[pIr1]:{
  pose proof ntSetComplete.
  intros n H0.
  destruct (nEq (lhs ru) n) as [Hreq|Hrneq].
- rewrite <- Hreq.
  rewrite ddInsertSame.
  left.
  firstorder. discriminate.
- rewrite <- pP2.
  rewrite <- ddInsertOther.
  apply pIr.
all:auto.
}
[pI2]:{ firstorder. }
[pIr2]:{
  pose proof uinEmpty.
  pose proof uEmptyEmpty.
  pose proof
    (@ddEmptyLookup N _ parseTreeDicFun (fun n0 : N => Nothing)).
  intros. right.
  firstorder.
}
[rI1]:{
  rewrite <- Heqr.
  rewrite ruleReassemble.
  auto.
}
Defined.

Definition rule_loop_body (nyfl:list N)
  (istate: nState nyfl) (*Workstack and Nullable dictionary
                                before the start of the function*)
  (irule: {r:rule N T | r ∊ G}): (*The actual rule to be processed*)
  nState nyfl.
   (*Return the modified work stack and nullable dictionary*)
refine (
  let '(nStateConstr _ workstack nullabledic pI pIr):=istate in
  let '(exist _ r pRInG):=irule in
  match ddlookup (lhs r) nullabledic as r0
  return ddlookup (lhs r) nullabledic=r0 -> _
  with
    | Just _ => fun Heq => istate
              (*The symbol is already on the nullable list*)
    | Nothing => fun Heq => (*we check the symbols on the rhs*)
    match rule_loop_body_aux (rhs r) nullabledic with 
      | Just x =>
        let '(exist _ ws1 pI1):=upush_in (lhs r) workstack ?[pInot] in
        nStateConstr nyfl
       (ws1)
       (ddinsert (lhs r) (Just (fun i k => ptNode G i (lhs r) _ k _ k (x i k) ?[Igr] ?[pEqb]))  nullabledic )
       ?[pI2] ?[pIr2]
    (*we found a new nullable symbol*)
      | Nothing => istate
    (*at least one of them is not yet nullable*)
    end
  end eq_refl
  ).

(*
[ptnode]:{
Eval cbv in (x i k).
Check(ptNode G i (lhs r) _ k _ k (x i k) ?[Igr] _).
assert (forall A (l:list A) (x:nat),x = last (fmap (fun _ : A => x) l) x) as Hkeq.
{
  induction l.
  reflexivity.
  intros.
  cbn.
  rewrite <- IHl.
  destruct l; reflexivity.
}
rewrite (Hkeq _ (rhs r) k) at 1.*)
[pInot]: { firstorder. }

[pI2]:{
  intros n.
  destruct (nEq (lhs r) n) as [Heq1|Hneq1].
  - rewrite Heq1 in Heq.
    firstorder.
  - assert (n <>lhs r) as Hneq2.
    auto.
    pose proof (fun v => ddInsertOther n (lhs r) v nullabledic Hneq2) as Hio.
    destruct pI1 as [H1 H2].
    pose proof (H2 _ Hneq1) as H3.
    rewrite <- H3.
    erewrite <- Hio.
    auto.
}
[pIr2]:{
  intros n.
  destruct (nEq (lhs r) n) as [Heq1|Hneq1].
  - intros H0.
    left.
    rewrite Heq1 in pI1.
    split.
    tauto.
    rewrite <- Heq1.
    rewrite ddInsertSame.
    discriminate.
  - assert (n <>lhs r) as Hneq2.
    auto.
    pose proof (fun v => ddInsertOther n (lhs r) v nullabledic Hneq2) as Hio.
    destruct pI1 as [H1 H2].
    pose proof (H2 _ Hneq1) as H3.
    rewrite <- H3.
    erewrite <- Hio.
    auto.
}
[Igr]:{
  rewrite ruleReassemble.
  exact pRInG.
}
[pEqb]:{
  destruct (rhs r); cbn; congruence.
}
Defined.


(**
In the symbol loop body we look up all the rules,
where the input symbol is in the rhs, and call the
rule loop on the list.
*)
Definition symbol_loop_body (nyfl:list N)
 (rhs_table:mdictionary N {r:rule N T | r ∊ G})
 (s:N)  (*The symbol that was just popped from the workstack*)
 (istate: nState nyfl)  (*Workstack before the start of the function*)
   (*Nullable dictionary
  before the start of the function*) :
  nState nyfl (*Return the modified work stack and
nullable dictionary*) :=
  let rl:= mlookup s rhs_table in
    foldl (rule_loop_body nyfl) istate rl.


Fixpoint symbol_loop
  (rhs_table:mdictionary N {r:rule N T | r ∊ G})
  (workstack: ustack N)  (*Workstack before the start of the function*)
  (nullabledic:parseTreeDic)
  (nyfl:list N) (*list of not yet finished symbols*)
  (pI: forall n,
    (n ∊ workstack \/ ddlookup n nullabledic = Nothing) ->
    n ∊ nyfl)
  (pIr: forall n, n ∊ nyfl ->
    (n ∊ workstack /\ ~ ddlookup n nullabledic = Nothing \/
    ddlookup n nullabledic = Nothing /\ ~ n ∊ workstack))
  (pAcc: Acc (ltof _ (@length N)) nyfl) {struct pAcc}
  : ustack N * parseTreeDic.
refine(
  match upop_in workstack with
    | inright H => (workstack, nullabledic)
    | inleft (exist _ (s,ws1) (conj pI1 (conj pI3 pI4))) =>
    let nyfl1 := @listDelete N nEq s nyfl in
    let '(nStateConstr _ ws2 nd2 pI2 pIr2) :=
        symbol_loop_body nyfl1 rhs_table s
        (nStateConstr nyfl1 ws1 nullabledic ?[pInew] ?[pIrnew]) 
    in symbol_loop rhs_table
         ws2 nd2 nyfl1 pI2 pIr2
        (Acc_inv pAcc ?[Rx])
  end
).

[pInew]:{
  intros n.
  destruct (nEq s n) as [Heq|Hneq].
- rewrite Heq in *.
  firstorder.
- intros H1.
  unfold nyfl1.
  apply deleteIn.
  auto.
  apply pI.
  rewrite pI4.
  auto.
  auto.
}
[pIrnew]:{
  intros n.
  destruct (nEq s n) as [Heq|Hneq].
- intros H.
  unfold nyfl1 in *.
  rewrite <- Heq in H.
  pose proof (@deleteNotIn _ nEq s nyfl).
  contradiction.
- intros H.
  rewrite <- (pI4 n Hneq).
  apply pIr.
  unfold nyfl1 in *.
  assert (n <> s) as Hneq2.
  auto.
  pose proof (@deleteIn _ nEq n s nyfl Hneq2).
  firstorder.
}
[Rx]:{
  unfold nyfl1.
  unfold ltof.
  apply deleteLength.
  firstorder.
}
Defined.



(**
Wrapper function, it creates the nullable lookup
function needed by the Earley parser.
*)
Definition createIsNullableMbParsetree: forall n:N, Maybe (forall i k, parseTreeDep N T G i k k n).
refine(
  let rhs_table := createRHSdic in
  let '(nStateConstr _ workstack nullabledic pI pIr) :=
    initializeState in
  let '(ws, finalnullabledic) := symbol_loop rhs_table workstack nullabledic ntSet pI pIr _ in
  fun n => ddlookup n finalnullabledic
).
apply well_founded_ltof.
Defined.

End grammarcontext.


Require Import Earley.exampleGrammars.

Notation "# a " := (exist _ a _) (at level 53).
Compute createRHSdic _ _ exGr2 _.
Definition isNullableExGr2 := createIsNullableMbParsetree _ _ ntSet2 ntSetComplete2 nEq2 exGr2 _ _.

Definition MB2bool {A} (x:Maybe A):=
match x with
  | Nothing => false
  | Just _ => true
end.
Time Compute isNullableExGr2 FC. 
Compute isNullableExGr2 FN.
Compute isNullableExGr2 ARGS.
Compute isNullableExGr2 ARG.
Compute isNullableExGr2 BB.
Compute isNullableExGr2 ARGL.
Time Compute MB2bool (isNullableExGr2 CC).

(*
Compute createNullableList exampleNonTerminals1 exampleTerminals1  exGr1 _.
Compute createNullableList exampleNonTerminals2 exampleTerminals2 exGr2 _.
*)



