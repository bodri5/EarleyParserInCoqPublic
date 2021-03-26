
(**
This file contains definitions about context free grammars.
*)
Require Import List.
Import ListNotations.
Require Import Bool.Sumbool.

Require Import Earley.datastructures.
(*Require Import Earley.listExtra.*)
Section alphabetcontext.

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
Instance nEqEqDecOpClass: EqDecOpClass N:=nEq.
Variable tEq: forall (t1 t2: T), {t1 = t2} + {t1 <> t2}.
Instance tEqEqDecOpClass: EqDecOpClass T:=tEq.
(**
A single grammar rule or production.
 *)
Inductive rule:=
  | ruleConstr (P:N) (a:list (N+T)) : rule.



(**
Getter functions for the left- and right-hand side of
the rule.
*)
Definition lhs (ru:rule): N:= let (l,_):=ru in l.

Definition rhs (ru:rule):list (N + T):= let (_,r):=ru in r.

Definition lrhs (ru:rule): N*list (N + T):= let (l,r):=ru in (l,r).

(**
Proof of correctness of the getters.
*)
Theorem ruleReassemble: forall r, (ruleConstr (lhs r) (rhs r))=r.
Proof.
  destruct r. reflexivity.
Qed.

Theorem ruleCreate: forall l r,
    lhs (ruleConstr l r)=l /\ rhs (ruleConstr l r)=r.
Proof.
  firstorder.
Qed.

Global Instance ruleEqDecOpClass: EqDecOpClass (rule).
intros [n1 rh1] [n2 rh2].
destruct (n1=?= n2).
destruct (rh1=?=rh2).
left. congruence.
right. congruence.
right. congruence.
Defined.

(**
Data type for context free grammars.
It contains a start symbol S, and a list
of rules.
*)
Inductive grammar:=
  | grammarConstr (s:N) (rules:list (rule)): grammar.

(**
Extractor functions.
*)
Definition grammarGetRules (g:grammar):=
  let (_,rules):= g in rules.

Definition grammarGetStart (g:grammar):=
  let (s,_):= g in s.


Section grammarcontext.
Variable G:grammar.

(**
The element at position n in the list is a.
*)
Inductive AtPos A (a:A): forall (l:list A) (pos:nat),Prop:=
  | atposHead l: AtPos A a (a::l) 0
  | atposTail b l (q:nat) (p:AtPos A a l q): AtPos A a (b::l) (S q).
Arguments AtPos [A] _ _ _.

Example atpos123example: AtPos 2 [1;2;3] 1.
  repeat constructor.
Qed.


Instance grammarruleInOpClass: InOpClass rule grammar:=
  fun r g => In r (grammarGetRules g).

Variable grammarruleInOpDecClass: InOpDecClass rule grammar grammarruleInOpClass.

Existing Instance grammarruleInOpDecClass.

Inductive parseTreeDep (i: list T):
    forall (bgnpos endpos: nat) (rootn:N),Type:=
  | ptNode
 (bgnpos endpos: nat)
 (rootn:N) (** This is the root non terminal symbol of the parsetree, and it is left hand side of the top grammar rule of this parsetree *)
      (rl: list (N+T)) (** This is the right hand side of the same grammar rule, and the list contains both non-terminal and terminal symbols. *)
      (t1: nat)
      (ts: list nat) (** This is the list of lists of terminal symbols which are covered by the children *)
      (ch: parseForestDep i t1 ts rl) (** This is the list of children *)
      (pM: (ruleConstr rootn rl) ∊ G) (** The pM gives a proof that the top rule is in the grammar *)
  :parseTreeDep i bgnpos endpos rootn
(** parseForestDep is essentially a list with additional information of the parse, pfNilWI is the nil constructor, pfSubTWI corresponds to cons with a non-terminal as head and pfTermWI corresponds to cons with a terminal as head *)
with parseForestDep (i: list T): nat->list nat->list (N+T)->Type:=
  | pfNil pos: parseForestDep i pos nil nil (** pfNilWI has no additional parameters *)
  | pfSub (** The first three inputs, tl,n and pt correspond to the head and the remaining ts,ns and pf correspond to the tail *)
       (b1 e1: nat) (** These are the start and end positions in the input covered by the first subtree *)
       (n1:N) (** This is the root symbol for the first subtree *)
       (pt:parseTreeDep i b1 e1 n1) (** This is the actual subtree *)
       (t1: nat)
       (ts: list nat) (** The list of inputs that are covered by the rest of the node *)
       (ns: list (N+T)) (** This is the list of root symbols that are covered by the rest of the node*)
       (pf:parseForestDep i t1 ts ns) (** These are the additional parsetrees of the tail *)
       (peq:e1=t1):
      parseForestDep i b1 (t1::ts) (inl n1::ns)
  | pfTrm
       (b1:nat)
       (c:T) (** The first symbol is the head which is a terminal symbol itself *)
       (t1: nat)
       (ts: list nat) (** The list of inputs that are covered by the rest of the node *)
       (ns: list (N+T)) (** This is the list of root symbols that are covered by the rest of the node*)
       (pf:parseForestDep i t1 ts ns) (** These are the additional parsetrees of the tail*)
       (p1:b1+1=t1)
       (pat:AtPos c i b1):
      parseForestDep i b1 (t1::ts) (inr c::ns).


(** Egy új node-t akarunk hozzátenni egy parseforesthez,
 vagyis egy szintaxisfát a parseforest végére. A függvény
 hozzáteszi a szabályhoz az új
 nemterminálist és a lefedett terminálisokhoz a hozzáadott
 fa által lefedetteket.

*)

Fixpoint ptSnocN (i: list T) bpos poss epos
    (ns : list (N+T)) (n : N)
    (pF:parseForestDep i bpos poss ns)
    (pT: parseTreeDep i (last poss bpos) epos n)  {struct pF}:
    parseForestDep i bpos (poss++[epos]) (ns++[inl n]).
refine(
  match pF as p in parseForestDep _ b q nl
  return bpos=b -> poss=q -> ns=nl -> parseForestDep i bpos (q++[epos]) (nl++[inl n])
  with
    | pfNil _ _ => fun Hbeq Hqeq Hneq => ?[pfnil]
    | pfSub _ b1 e1 n1 pt t1 ts1 ns1 pf pEq =>
        fun Hbeq Hqeq Hneq => ?[pfsub]
    | pfTrm _ b1 c t1 ts1 ns1 pf pEq pAt =>
        fun Hbeq Hqeq Hneq => ?[pftrm]
  end eq_refl eq_refl eq_refl
).
[pfnil]:{
rewrite Hqeq in pT.
cbn in pT |- *.
apply (pfSub i bpos epos n pT epos nil nil (pfNil _ _) eq_refl).
}
[pfsub]:{
  simpl.
  rewrite Hbeq.
  eapply(pfSub i _ _ _ pt _ _ _ (ptSnocN _ _ _ _ _ _ pf ?[pT]) pEq).
  [pT]:{
    erewrite <- lastCons.
    rewrite <- Hqeq.
    exact pT.
  }
}
[pftrm]:{ rewrite <- Hbeq in pEq, pAt.
eapply (pfTrm i bpos c t1 _ _ (ptSnocN _ _ _ _ _ _ pf ?[pT]) pEq pAt).
  [pT]:{
    erewrite <- lastCons.
    rewrite <- Hqeq.
    exact pT.
  }
}
Defined.


(** A ptSnocT függvény egy terminális szimbólumból álló
 parseForestet tesz hozzá a parseForest végéhez,
 hozzátéve a terminális szimbólumot mind
két listához.

*)

Fixpoint ptSnocT (*(ts : list (list T)) (ns : list (N+T))
   (pF:parseForestDep ts ns) (t:T):
    parseForestWithInput(ts++[[t]])(ns ++ [inr t]):=*)

 (i: list T) bpos poss epos
    (ns : list (N+T))
    (pF:parseForestDep i bpos poss ns) (t:T)
    (pEq:(last poss bpos)+1=epos) (pAt:AtPos t i (last poss bpos)) {struct pF}:
    parseForestDep i bpos (poss++[epos]) (ns++[inr t]).

refine(
  match pF as p in parseForestDep _ b q nl
  return bpos=b -> poss=q -> ns=nl -> parseForestDep i bpos (q++[epos]) (nl++[inr t])
  with
    | pfNil _ _ => fun Hbeq Hqeq Hneq => ?[pfnil]
    | pfSub _ b1 e1 n1 pt t1 ts1 ns1 pf pEq =>
        fun Hbeq Hqeq Hneq => ?[pfsub]
    | pfTrm _ b1 c t1 ts1 ns1 pf pEq pAt =>
        fun Hbeq Hqeq Hneq => ?[pftrm]
  end eq_refl eq_refl eq_refl
).

[pfnil]:{
subst.
cbn in *.
refine ((pfTrm i _ t _ _ _ (pfNil _ _) eq_refl pAt)).
}
[pfsub]:{
  simpl.
  rewrite Hbeq.
  refine (pfSub i _ _ _ pt _ _ _ (ptSnocT _ _ _ _ _ pf t ?[pEq1] ?[pAt1]) pEq).
  [pEq1]:{
    erewrite <- lastCons.
    rewrite <- Hqeq.
    exact pEq0.
  }
  [pAt1]:{
  erewrite <- lastCons.
  rewrite <- Hqeq.
  exact pAt.
  }
}
[pftrm]:{ rewrite <- Hbeq in pEq, pAt.
eapply (pfTrm i bpos c t1 _ _ (ptSnocT _ _ _ _ _ pf t ?[pEq1] ?[pAt1]) pEq pAt).
  [pEq1]:{
    erewrite <- lastCons.
    rewrite <- Hqeq.
    exact pEq0.
  }
  [pAt1]:{
  erewrite <- lastCons.
  rewrite <- Hqeq.
  exact pAt0.
  }
}
Defined.



End grammarcontext.
End alphabetcontext.


Arguments ruleConstr {N T} _ _.
Arguments lhs {N T} _.
Arguments rhs {N T} _.
Arguments grammarConstr {N T} _ _.
Arguments grammarGetRules {N T} _.
Arguments grammarGetStart {N T} _.
Arguments ptNode {N T} _ _.


