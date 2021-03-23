
Require Import List.
Import ListNotations.

Require Import Earley.datastructures.
Require Import Earley.grammarDep.

Inductive exampleTerminals1:=
  | num (n:nat)
  | tplus
  | tminus
  | tmul
  | tdiv
  | popen
  | pclose
.
Inductive exampleNonTerminals1:=
  | tS
  | tK
  | tN
  | tStart.

Instance example1MultiDictionary:MultiDictionary exampleNonTerminals1:=
{
  mdictionary V:= ((list V)*(list V)*(list V)*(list V))%type;
  memptyDictionary {V} := (nil,nil,nil,nil);
  minsert {V} k v dic :=
    match k, dic with
      | tS, (a,b,c,d) => (v::a,b,c,d)
      | tK, (a,b,c,d) => (a,v::b,c,d)
      | tN, (a,b,c,d) => (a,b,v::c,d)
      | tStart, (a,b,c,d) => (a,b,c,v::d)

    end;
  mlookup {V} k dic :=
    match k, dic with
      | tS, (a,b,c,d) => a
      | tK, (a,b,c,d) => b
      | tN, (a,b,c,d) => c
      | tStart, (a,b,c,d) => d

    end;
}.

Instance example1OverwriteDictionary:OverwriteDictionary  exampleNonTerminals1:=
{
  odictionary V:= ((Maybe V)*(Maybe V)*(Maybe V)*(Maybe V))%type;
  oemptyDictionary {V} := (Nothing,Nothing,Nothing,Nothing);
  oinsert {V} k v dic :=
    match k, dic with
      | tS, (a,b,c,d) => (Just v,b,c,d)
      | tK, (a,b,c,d) => (a,Just v,c,d)
      | tN, (a,b,c,d) => (a,b,Just v,d)
      | tStart, (a,b,c,d) => (a,b,c,Just v)

    end;
  olookup{V} k dic :=
    match k, dic with
      | tS, (a,b,c,d) => a
      | tK, (a,b,c,d) => b
      | tN, (a,b,c,d) => c
      | tStart, (a,b,c,d) => d

    end;
}.
Definition inlcoerce1 (x:exampleNonTerminals1):=
    inl exampleTerminals1 x.
Definition inrcoerce1 (x:exampleTerminals1):=
    inr exampleNonTerminals1 x.

Coercion inlcoerce1: exampleNonTerminals1 >-> sum.

Coercion inrcoerce1: exampleTerminals1 >-> sum.

Notation "x → y , .. , z" :=
  (ruleConstr x
     (@cons (_+_)
       y ..
       (@cons (_+_)
        z (@nil (_+_))) .. ) )
  (at level 60).
Notation "x → 'epsilon'" :=
  (ruleConstr x []) (at level 60).

Definition exGr1:=
  grammarConstr
    tK  (*Start symbol*)
    [   (*List of production rules*)
      tK → tK , tplus , tS;
      tK → tK , tminus , tS;
      tK → tS;
      tS → tS , tmul , tN;
      tS → tS , tdiv , tN;
      tS → tN;
      tN → popen , tK, pclose;
      tN → num 0;
      tN → num 1;
      tN → num 2;
      tN → num 3;
      tN → num 4;
      tN → num 5;
      tN → num 6
    ].

Inductive exampleTerminals2:=
  | arg2
  | fun2
  | comma2
  | popen2
  | pclose2
.

Inductive exampleNonTerminals2:=
  | FC
  | FN
  | ARGS
  | ARG
  | BB
  | ARGL
  | CC.

Definition nEq2:forall (n1 n2: exampleNonTerminals2),
    {n1 = n2} + {n1 <> n2}.
destruct n1,n2;
firstorder || right;congruence.
Defined.

Definition ntSet2:=[FC;FN;ARGS;ARG;BB;ARGL;CC].
Lemma ntSetComplete2: forall n, n ∊ ntSet2.
  destruct n;
  firstorder.
Qed.

Instance example2MultiDictionary: MultiDictionary exampleNonTerminals2:=
{
  mdictionary V:= ((list V)*(list V)*(list V)*(list V)*(list V)*(list V)*(list V))%type;
  memptyDictionary {V} := (nil,nil,nil,nil,nil,nil,nil);
  minsert {V} (k:exampleNonTerminals2) (v:V)
    dic :=
    match k, dic with
      | FC,   (a,b,c,d,e,f,g) => (v::a,b,c,d,e,f,g)
      | FN,   (a,b,c,d,e,f,g) => (a,v::b,c,d,e,f,g)
      | ARGS, (a,b,c,d,e,f,g) => (a,b,v::c,d,e,f,g)
      | ARG,  (a,b,c,d,e,f,g) => (a,b,c,v::d,e,f,g)
      | BB,   (a,b,c,d,e,f,g) => (a,b,c,d,v::e,f,g)
      | ARGL, (a,b,c,d,e,f,g) => (a,b,c,d,e,v::f,g)
      | CC,   (a,b,c,d,e,f,g) => (a,b,c,d,e,f,v::g)   
    end;
  mlookup{V} (k:exampleNonTerminals2)
    dic :=
    match k, dic with
      | FC,   (a,b,c,d,e,f,g) => a
      | FN,   (a,b,c,d,e,f,g) => b
      | ARGS, (a,b,c,d,e,f,g) => c
      | ARG,  (a,b,c,d,e,f,g) => d
      | BB,   (a,b,c,d,e,f,g) => e
      | ARGL, (a,b,c,d,e,f,g) => f
      | CC,   (a,b,c,d,e,f,g) => g
    end;
}.

Instance example2OverwriteDictionary: OverwriteDictionary  exampleNonTerminals2:=
{
  odictionary V:= ((Maybe V)*(Maybe V)*(Maybe V)*(Maybe V)*(Maybe V)*(Maybe V)*(Maybe V))%type;
  oemptyDictionary {V} := (Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing);
  oinsert {V} (k:exampleNonTerminals2) (v:V)
    dic :=
    match k, dic with
      | FC,   (a,b,c,d,e,f,g) => (Just v,b,c,d,e,f,g)
      | FN,   (a,b,c,d,e,f,g) => (a,Just v,c,d,e,f,g)
      | ARGS, (a,b,c,d,e,f,g) => (a,b,Just v,d,e,f,g)
      | ARG,  (a,b,c,d,e,f,g) => (a,b,c,Just v,e,f,g)
      | BB,   (a,b,c,d,e,f,g) => (a,b,c,d,Just v,f,g)
      | ARGL, (a,b,c,d,e,f,g) => (a,b,c,d,e,Just v,g)
      | CC,   (a,b,c,d,e,f,g) => (a,b,c,d,e,f,Just v)
    end;
  olookup{V} (k:exampleNonTerminals2)
    dic :=
    match k, dic with
      | FC,   (a,b,c,d,e,f,g) => a
      | FN,   (a,b,c,d,e,f,g) => b
      | ARGS, (a,b,c,d,e,f,g) => c
      | ARG,  (a,b,c,d,e,f,g) => d
      | BB,   (a,b,c,d,e,f,g) => e
      | ARGL, (a,b,c,d,e,f,g) => f
      | CC,   (a,b,c,d,e,f,g) => g
    end;
}.

Instance example2DefaultDictionary: DefaultDictionary  exampleNonTerminals2:=
{
  ddictionary V:= ((V)*(V)*(V)*(V)*(V)*(V)*(V))%type;
  demptyDictionary {V} d := (d,d,d,d,d,d,d);
  dinsert {V} (k:exampleNonTerminals2) (v:V)
    dic :=
    match k, dic with
      | FC,   (a,b,c,d,e,f,g) => (v,b,c,d,e,f,g)
      | FN,   (a,b,c,d,e,f,g) => (a,v,c,d,e,f,g)
      | ARGS, (a,b,c,d,e,f,g) => (a,b,v,d,e,f,g)
      | ARG,  (a,b,c,d,e,f,g) => (a,b,c,v,e,f,g)
      | BB,   (a,b,c,d,e,f,g) => (a,b,c,d,v,f,g)
      | ARGL, (a,b,c,d,e,f,g) => (a,b,c,d,e,v,g)
      | CC,   (a,b,c,d,e,f,g) => (a,b,c,d,e,f,v)
    end;
  dlookup{V} (k:exampleNonTerminals2)
    dic :=
    match k, dic with
      | FC,   (a,b,c,d,e,f,g) => a
      | FN,   (a,b,c,d,e,f,g) => b
      | ARGS, (a,b,c,d,e,f,g) => c
      | ARG,  (a,b,c,d,e,f,g) => d
      | BB,   (a,b,c,d,e,f,g) => e
      | ARGL, (a,b,c,d,e,f,g) => f
      | CC,   (a,b,c,d,e,f,g) => g
    end;
}.

#[refine]
Instance example2DependentDefaultDictionary:DependentDefaultDictionary  exampleNonTerminals2:=
{
  dddictionary V:= ((V FC)*(V FN)*(V ARGS)*(V ARG)*(V BB)*(V ARGL)*(V CC))%type;
  ddemptyDictionary {V} d := (d FC,d FN,d ARGS,d ARG,d BB,d ARGL,d CC);
  ddinsert {V} (k:exampleNonTerminals2) (v:V k)
    dic :=
    match dic, k as k0 
    return V k0 -> _
    with
      | (a,b,c,d,e,f,g), FC   => fun v => (v,b,c,d,e,f,g)
      | (a,b,c,d,e,f,g), FN   => fun v => (a,v,c,d,e,f,g)
      | (a,b,c,d,e,f,g), ARGS => fun v => (a,b,v,d,e,f,g)
      | (a,b,c,d,e,f,g), ARG  => fun v => (a,b,c,v,e,f,g)
      | (a,b,c,d,e,f,g), BB   => fun v => (a,b,c,d,v,f,g)
      | (a,b,c,d,e,f,g), ARGL => fun v => (a,b,c,d,e,v,g)
      | (a,b,c,d,e,f,g), CC   => fun v => (a,b,c,d,e,f,v)
    end v;
  ddlookup{V} (k:exampleNonTerminals2)
    dic :=
    match k, dic with
      | FC,   (a,b,c,d,e,f,g) => a
      | FN,   (a,b,c,d,e,f,g) => b
      | ARGS, (a,b,c,d,e,f,g) => c
      | ARG,  (a,b,c,d,e,f,g) => d
      | BB,   (a,b,c,d,e,f,g) => e
      | ARGL, (a,b,c,d,e,f,g) => f
      | CC,   (a,b,c,d,e,f,g) => g
    end;
  ddInsertSame V k v dic:=?[ddInsertSame];
  ddInsertOther V k k1 v1 dic:=?[ddInsertOther];
  ddEmptyLookup V df k:=?[ddEmptyLookup];
}.
[ddInsertSame]:{
destruct k;
destruct dic as [[[[[[a b] c] d] e] f] g];
reflexivity.
}
[ddInsertOther]:{
destruct k;
destruct dic as [[[[[[a b] c] d] e] f] g];
destruct k1; auto; contradiction.
}
[ddEmptyLookup]:{
destruct k; reflexivity.
}
Defined.



Definition inlcoerce2 (x:exampleNonTerminals2):=inl exampleTerminals2 x.
Definition inrcoerce2 (x:exampleTerminals2):=inr exampleNonTerminals2 x.

Coercion inlcoerce2: exampleNonTerminals2 >->
  sum.

Coercion inrcoerce2: exampleTerminals2 >->
  sum.


Definition exGr2:=
  grammarConstr
    FC  (*Start symbol*)
    [   (*List of production rules*)
      FC   → FN , popen2 , ARGS, pclose2;
      ARGS → epsilon ;
      ARGS → ARGL;
      ARGL → ARG;
      ARGL → ARG , comma2 , ARGL;
      BB   → ARGS , ARGS;
      ARG  → arg2;
      FN   → fun2;
      CC   → ARG;
      CC   → BB , BB
    ].
