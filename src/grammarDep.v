
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
  (rootn:N) (** This is the root non terminal symbol of the
     parsetree, and it is theleft hand side of the top grammar
     rule of this parsetree. *)
  (rl: list (N+T)) (** This is the right hand side of the same
     grammar rule, and the list contains both non-terminal and
     terminal symbols. *)
  (bpos:nat) (*Start position*)
  (poss: list nat) (**Start positions between the rhs symbols
     in the input. *)
  (epos: nat) (** Last position covered in the input by
     this parsetree. *)
  (ch: parseForestDep i poss epos rl) (** This is the list of
     children *)
  (pM: (ruleConstr rootn rl) ∊ G) (** The pM gives a proof that
     the rule is in the grammar *)
  (pEqb:bpos = hd epos poss)
     (*the two start  positions must match*)
  :parseTreeDep i bpos epos rootn
(** parseForestDep is essentially a list with additional information of the parse, pfNilWI is the nil constructor, pfSubTWI corresponds to cons with a non-terminal as head and pfTermWI corresponds to cons with a terminal as head *)
with parseForestDep (i: list T): list nat->nat->
  list (N+T)->Type:=
  | pfNil pos: parseForestDep i nil pos nil (** Empty forest at
       position pos *)
  | pfSub (** Cons operation with a nonterminal at the head. *)
  (b1 e1: nat) (** These are the start and end positions
     in the input covered by the first subtree. e1 is also the
     first position of the tail. *)
  (n1:N) (** This is the root symbol for the first subtree *)
  (pt:parseTreeDep i b1 e1 n1) (** This is the actual subtree. *)
  (poss: list nat) (**Start positions between the rhs symbols
     in the input. *)
  (epos: nat) (** Last position covered in the input by
     this parsetree. *)
  (ns: list (N+T)) (** This is the list of root symbols that are
    covered by the rest of the node. *)
  (pf:parseForestDep i poss epos ns) (** These are the additional
    parsetrees of the tail *)
  (pEqb:e1 = hd epos poss):
      parseForestDep i (b1::poss) epos (inl n1::ns)
  | pfTrm (** Cons operation with a terminal at the head. *)
       (b1:nat)
       (c:T) (** The first symbol is the head which is a terminal symbol itself *)
       (poss: list nat) (** The list of inputs that are covered by the rest of the node *)
       (epos: nat)
       (ns: list (N+T)) (** This is the list of root symbols that are covered by the rest of the node*)
       (pf:parseForestDep i poss epos ns) (** These are the additional parsetrees of the tail*)
       (p1:b1+1 = hd epos poss)
       (pat:AtPos c i b1):
      parseForestDep i (b1::poss) epos (inr c::ns).


(** 
Appends a new nonterminal and the corresponding parstee
to the end of the parseforest.
*)
Fixpoint ptSnocN (i: list T) poss epos eepos
    (ns : list (N+T)) (n : N)
    (pF:parseForestDep i poss epos ns)
    (pT: parseTreeDep i epos eepos n)  {struct pF}:
    parseForestDep i (poss++[epos]) eepos (ns++[inl n]).
refine(
  match pF as p in parseForestDep _ poss0 epos0 ns0
  return poss=poss0 -> epos=epos0 -> ns=ns0 -> parseForestDep i
    (poss0++[epos]) eepos (ns0++[inl n])
  with
    | pfNil _ _ => fun Hbeq Hqeq Hneq =>
       pfSub i epos eepos n pT nil eepos nil (pfNil _ eepos) eq_refl
    | pfSub _ b1 e1 n1 pt poss1 epos1 ns1 pf pEqb =>
        fun Hbeq Hqeq Hneq => ?[pfsub]
    | pfTrm _ b1 c poss1 epos1 ns1 pf pEqb pAt =>
        fun Hbeq Hqeq Hneq => ?[pftrm]
  end eq_refl eq_refl eq_refl
).
(*[pfnil]:{
eapply (pfSub i epos eepos n pT nil eepos nil (pfNil _ eepos) eq_refl).
rewrite Hqeq in pT.
cbn in pT |- *.
apply (pfSub i epos eepos n pT nil eepos (pfNil _ eepos) _).
}*)
[pfsub]:{
  simpl.
  rewrite <- Hqeq in pf.
  eapply
    (pfSub i _ _ _ pt _ eepos _ (ptSnocN _ _ _ _ _ n pf pT) ?[pEqb]).
  [pEqb]:{
    destruct poss1;
    cbn in *;
    congruence.
  }
}
[pftrm]:{
  simpl.
  rewrite <- Hqeq in pf.
  eapply
    (pfTrm i b1 c _ _ _ (ptSnocN _ _ _ _ _ n pf pT) ?[pEqb] pAt).
  [pEqb]:{
    destruct poss1;
    cbn in *;
    congruence.
  }
}
Defined.


(** 
Appends a new terminal to the end of the parseforest.
A proof that there is really the given character at
the given position in the input must be given.
*)
Fixpoint ptSnocT
    (i: list T) poss epos
    (ns : list (N+T))
    (pF:parseForestDep i poss epos ns) (t:T)
    (pAt:AtPos t i epos) {struct pF}:
    parseForestDep i (poss++[epos]) (epos+1) (ns++[inr t]).
refine(
  match pF as p in parseForestDep _ poss0 epos0 ns0
  return poss=poss0 -> epos=epos0 -> ns=ns0 -> parseForestDep i
    (poss0++[epos]) (epos0+1) (ns0++[inr t])
  with
    | pfNil _ epos1 => fun Hbeq Hqeq Hneq => (*?[pfnil]*)
       pfTrm i epos t [] (epos1+1)  nil (pfNil _ _) (ltac:(cbn in *;congruence)) pAt
    | pfSub _ b1 e1 n1 pt poss1 epos1 ns1 pf pEqb =>
        fun Hbeq Hqeq Hneq => ?[pfsub]
    | pfTrm _ b1 c poss1 epos1 ns1 pf pEqb pAt1 =>
        fun Hbeq Hqeq Hneq => ?[pftrm]
  end eq_refl eq_refl eq_refl
).
[pfsub]:{
  simpl.
  rewrite <- Hqeq in *.
  eapply
    (pfSub i _ _ _ pt _ (epos+1) _ (ptSnocT _ _ _ _ pf t pAt)
       ?[pEqb]).
  [pEqb]:{
    destruct poss1;
    cbn in *;
    congruence.
  }
}
[pftrm]:{
  simpl.
  rewrite <- Hqeq in *.
  eapply
    (pfTrm i b1 c _ _ _ (ptSnocT _ _ _ _ pf t pAt) ?[pEqb] pAt1).
  [pEqb]:{
    destruct poss1;
    cbn in *;
    congruence.
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


