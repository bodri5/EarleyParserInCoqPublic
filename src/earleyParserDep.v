(** Az earleyParser file változásai

*)

Require Import List.
Import ListNotations.
Require Import Psatz.

Require Import Earley.datastructures.
Require Import Earley.grammarDep.


Require Import Bool.Sumbool.
Require Import Arith.
Open Scope bool_scope.

Section Earleycontext.
Variable N T:Type.
Variable G:grammar N T.

(*TODO it should be visible from grammarDep*)
Instance grammarruleInOpClass: InOpClass (rule N T) (grammar N T):=
  fun r g => In r (grammarGetRules g).

Variable i:list T. (*The input string*)

(** A két összehasonlító függvény már nem bool adattipussal tér vissza hanem sumbool-al, ami tartalmassa a bizonyítékot is. A subool valójában vagy egy bizonyítékot ad vissza arra hogy igaz vagy egyet arra hogy hamis.

*)
Variable nEq: forall (n1 n2: N), {n1 = n2} + {n1 <> n2}.
Instance nEqEqDecOpClass: EqDecOpClass N:=nEq.
Variable tEq: forall (t1 t2: T), {t1 = t2} + {t1 <> t2}.
Instance tEqEqDecOpClass: EqDecOpClass T:=tEq.

(**
Ha nullázható a megadott nemterminális szimbólum, visszaad
egy ennek megfelelő szintaxisfát.
*)
Variable isNullable: forall (n:N), Maybe (forall i k, parseTreeDep N T G i k k n).


(** Az earley item jelentősen megváltozott. Az általa tartalmazott szabály szét lett bontva 3 részre. Külön áll a bal oldal, a jobb oldal pont előtti és a pont utáni részei. Ezen túl tartalmazza az általa lefedett netminálisok listáját. Továbbra is tartalmazza az általa generált parsetreeket, most már parseForest típusban, és a származási set számát, vagy mászoóval, hogy hányadik szimbólumnál kezdődik az elemzés amit lefed az item. Tartalmaz még kettő bizonylatot, egyet arra hogy az általa lefedett terminálisok listája megegyezik az elemzendő listában levőkkel, az item kezdő pozíciótól indulva. A másik pedig azt bizonyítja, hogy az item által lefedett szabály (a 3 részből összeillesztve) része a nyelvtannak.

*)
Inductive earlyItemD:=
  eiC (n:N)
  (startposition:nat)
  (rns: list (N+T))
  (rnp: list nat)
  (pf: parseForestDep N T G i startposition rnp rns)
  (pnd: list (N+T)) (*Stuff after the dot*)
  (pM: (ruleConstr n (rns++pnd)) ∊ G).

Notation "n → rns • pnd ( k ) , ks pf pI" :=
  (eiC n k rns ks pf pnd pI)  (only printing, at level 60).




(** Függvények az earley item különböző részeinek kiszedésére.

*)


Definition eitGetRule (it:earlyItemD):= 
  let (n,start,rns,rnp,pf,pnd,pM):=it in ruleConstr  n (rns++pnd).


(**The position of the dot.*)
Definition eitGetPOD (it:earlyItemD):= 
  let (n,start,rns,rnp,pf,pnd,pM):=it in length rns.

Definition eitGetStartposition (it:earlyItemD):= 
  let (n,start,rns,rnp,pf,pnd,pM):=it in start.

(*?????*)
(*Definition eitExtrCH (it:earlyItemD): sigT (fun ris: (list (list T)) => sigT (fun rns=> parseForestWithInput N T G ris rns)):= 
  let (_,ris,rns,pf,_,_,_,_):=it in existT _ ris (existT _ rns pf).
*)

Definition eitGetPending (it:earlyItemD):= 
  let (n,start,rns,rnp,pf,pnd,pM):=it in pnd.

(*
Definition eitExtrRis (it:earlyItemD):= 
  let (_,ris,_,_,_,_,_,_):=it in ris.*)

Definition eitGetEndPos (it:earlyItemD):= 
  let (n,start,rns,rnp,pf,pnd,pM):=it in last rnp start.

(** A befejezett earley set-ekhez hozzá került a set száma, és egy bizonyítás, hogy az általa lefedett terminálisok a kadik nál érnek véget.

*)

Definition completedEarleySets := 
  list {k:nat & list {it:earlyItemD | eitGetEndPos it = k}}.

(*
Instance ruleEqDecOpClass: EqDecOpClass (rule N T).
intros [n1 rh1] [n2 rh2].
destruct a.
Admitted.*)

Existing Instance ruleEqDecOpClass.

Definition eiEq (ei1 ei2:earlyItemD): bool.
refine(
  Nat.eqb (eitGetStartposition ei1) (eitGetStartposition ei2) &&
  Nat.eqb (eitGetPOD ei1) (eitGetPOD ei2) &&
  (if (eitGetRule ei1) =?= (eitGetRule ei2) then true else false)
).
(*Coq should be able to find it automatically!*)
eapply ruleEqDecOpClass; auto.
Defined.

(** Az éppen elemzett itemek listájához is hozzákerült ugyanaz mint a befejezettekhez.

*)

Inductive earleySetUnderConstruction: nat->Type:=
    sucC k (completed:(list {it:earlyItemD | eitGetEndPos it = k}))
         (pending:(list {it:earlyItemD | eitGetEndPos it = k})):
  earleySetUnderConstruction k.

Definition getNextUnprocessed k (s:earleySetUnderConstruction k):=
  match s with
    | sucC k c p =>
    match p with 
      | nil => Nothing
      | cons h _ => Just h
    end
  end.

Definition markAsCompleted k (s:earleySetUnderConstruction k):
  earleySetUnderConstruction k:=
  match s in earleySetUnderConstruction k0 return earleySetUnderConstruction k0 with
    | sucC k c p =>
    match p with 
      | nil => sucC k c p
      | cons h t => sucC k (cons h c) t
   end 
  end.


Fixpoint isItemInList k
 (i:earlyItemD) (items:list {it:earlyItemD | eitGetEndPos it = k}):bool :=
  match items with 
    |cons (exist _ hd _) tl => 
      if eiEq hd i 
      then true
      else isItemInList k i tl
    | nil => false
    end.

(** Az insertIntoESC függvény az earley item mellé a szükséges bizonyítást is beleteszi a listába. Ezt bemenő paraméterként kapja meg.

*)

Fixpoint insertIntoESC 
  k (e:earleySetUnderConstruction k) (ni:earlyItemD) (prf: eitGetEndPos ni = k):  
      earleySetUnderConstruction k.
refine(
    match e in earleySetUnderConstruction k0 return k=k0 -> earleySetUnderConstruction k0 with 
          | sucC k1 comp pend => fun heq =>
            match (isItemInList k1 ni comp) , 
                  (isItemInList k1 ni pend) with 
              | false, false => sucC k1 comp (pend ++  [exist _ ni _])
              | _,_ => sucC k1 comp pend
            end
    end eq_refl
).
rewrite <- heq.
exact prf.
Defined.

(** Ez a függvény továbbra is a pont utáni első elemet olvassa ki, ami most a pont utáni szimbólumok listájának az első eleme. Hogyha nincs következő elem, bizonyítékot adunk vissza arra, hogy a szabálynak nincs több megvizsgálandü eleme.

*)
Definition getNextSymbolFromEarleyItem (it:earlyItemD): (N+T) + {eitGetPending it = nil}.
refine (
  (let (n,start,rns,rnp,pf,pnd,pM) as k return it = k -> _ := it in fun ieq =>
      match pnd as pend return pnd = pend -> _ with 
        | nil => fun heq => inright _ 
        | cons hd _ => fun heq => inleft hd
      end eq_refl) 
  eq_refl
).
try rewrite ieq. (*needed for version 8.6 coq*)
simpl.
exact heq.
Defined.

(** Ez a függvény a befejezett earley setek közül visszaadja a k-adikat.

*)

Fixpoint getKfromCes k (ces:completedEarleySets): list {it:earlyItemD | eitGetEndPos it = k}.
refine (
  match ces with
    | nil=> nil
    | cons (existT _ k0 hd) tl => 
    match Nat.eq_dec k k0  with 
      | left _ => _
      | right _ => getKfromCes k tl
    end
  end
).
rewrite e.
exact hd.
Defined.

(** A lookup a megfelelő itemek mellé tesz két bizonyítékot is, arra hogy a következő szimbólum valóban a megfelelő nemterminális, ittelve a bizonyíték hogy az adott setnél van a feldolgozott terminálisok vége.
*)


Fixpoint lookupAux (pos:nat) (eil:list {it:earlyItemD | eitGetEndPos it = pos}) (B:N) {struct eil}:
(list ({it : earlyItemD | getNextSymbolFromEarleyItem it = inleft (inl B) /\ eitGetEndPos it = pos})).
refine(
  match eil with
    | cons (exist _ hd prf) tl => 
    match getNextSymbolFromEarleyItem hd as pr 
    return getNextSymbolFromEarleyItem hd = pr -> _ 
    with
      | inleft (inl x) => fun heq => if nEq x B then 
    
        cons (exist _ hd _) (lookupAux pos tl B)
   else lookupAux pos tl B 
      | _ => fun heq => lookupAux pos tl B
    end eq_refl
    | nil => nil
  end
).
split.
rewrite <- e.
exact heq.
exact prf.
Defined.


Fixpoint lookup (ces:completedEarleySets) (B:N) (pos:nat):
(list ({it : earlyItemD | getNextSymbolFromEarleyItem it = inleft (inl B) /\ eitGetEndPos it = pos})).
refine (
  match ces with
    | nil => nil
    | cons (existT _ k hd) tl => 
    match Nat.eq_dec k pos with 
      | left _ =>_ 
      | right _ => lookup tl B pos
    end
  end
).
rewrite <- e.
exact (lookupAux k hd B).
Defined.

(** A part of input függvény bool helyett sumbool típust ad vissza.

*)


Fixpoint AtPosDec (t:T) (ii:list T) (k:nat):
{AtPos T t ii k}+{~AtPos T t ii k}.
refine(
  match k as k0, ii as ii0
  return {AtPos T t ii0 k0}+{~AtPos T t ii0 k0}
  with 
    | S n, cons hd tl =>
        if AtPosDec t tl n then left _ else right _
    | O, hd :: tl => if tEq hd t then left _ else right _
    | _,_ => right _
    end
).
intros H.
inversion H.
rewrite e.
apply atposHead.
intros H.
inversion H.
congruence.
intros H.
inversion H.
apply (atposTail _ _ _ _ _ a).
intros H.
inversion H.
congruence.
Defined.



(** A dotacvancer is jelentős változásokon ment keresztül, az earley item változtatása miatt. A pont mozgatásához hozzá kell adnunk a lefedett terminálisokhoz az újonnan lefedetteket, és szolgáltatni kell az earley itemhez tartozó kettő bizonyítékot, illetve a parseforesthez hozzá kell tenni a a megfelelő szintaxisfát. Ezen túl a pont mozgatása is megváltozott, hiszen nem egy szémot kell növelni, hanem áttenni a szabály még nem elemzett részének az első elemét a már elemzettek végére. Bejövő paraméterként kapjuk a lefedett terminálisok listáját, a nemterminálist amin túlmozgatjuk a pontot, a szintaxisfát ami ábrázolja a lefedett terminálisokat, az itemet amiben mozgatjuk a pontot. Illetve bizonyítékot hogy tényleg a megfelelő nemterminális áll a pont után, és hogy a lefedett terminálisok, a megfelelő pozícióban részei az elemzendő szövegnek.

*)
Definition dotAdvancerN
  (bpos epos: nat) (*The input, covered by the new part*)
  (b:N)           (*Nonterminal symbol, were the dot is advanced*)
  (ch:parseTreeDep N T G i bpos epos b)
                  (*The parsetree that parses the input*)
  (it:earlyItemD) (*Earley item subject to dot advacement*)
  (nip : getNextSymbolFromEarleyItem it = inleft (inl b))
             (*Proof that really there is a b after the dot in it*)
  (iinp : (eitGetEndPos it) = bpos)
             (*Proof, thet input really is part of the whole
                 imput at the apropriate position*)
    : earlyItemD. (*Return it modified with the dot advanced
                    one position*)
refine ( 
  match it as k
  return it = k ->
         getNextSymbolFromEarleyItem k = inleft (inl b)->
         earlyItemD
  with eiC n start rns rnp pf pnd pM => fun ieq neq => 
    match pnd as remsymb
    return pnd = remsymb ->
           forall pM2,
           getNextSymbolFromEarleyItem (eiC n start rns rnp pf remsymb pM2 ) =
           inleft (inl b) ->
           earlyItemD
    with 
      | nil => fun heq hpm neq2 => it
      | cons hd tl => fun heq hpm neq2 =>
        eiC n start (rns ++ [hd]) (rnp ++ [epos]) _ tl _
    end eq_refl pM neq
  end eq_refl nip


).
simpl in neq2.
assert (be : hd = inl b).
injection neq2.
auto.
rewrite be.

rewrite ieq in iinp.
cbn in iinp.
rewrite <- iinp in ch.
exact (ptSnocN _ _ _ _ _ _ _ _ _ pf ch).

rewrite <- app_assoc.
apply hpm.
Defined.



(** Egy bizonyatott tétel arra, hogy ha a a dotadvancert nullázható nemterminálisra használjuk, ahol a lefedett terminálisok listája az üres lista, akkor az eddig lefedett terminálisok listájának a vége nem változik.

*)

Theorem dotadvancerNul:
 forall bpos n x ei heq prf, eitGetEndPos (dotAdvancerN bpos bpos n x ei heq prf) = eitGetEndPos ei.
Proof.
  intros bpos n x ei heq prf.
  destruct ei.
  simpl.
  destruct pnd.
  simpl.
  reflexivity.
  simpl.
  simpl in prf.
  rewrite last_last.
  auto.
Qed.

(** Egy bebizonyított tétel, hogy a dotadvancer haszálata után, az utolsó lefedett terminális pozíciója megegyezik az item által utoljára lefedett szimbóluméval

*)
(*
eitGetEndPos
  (dotAdvancerN x k inn (ptNode G i x k inn irns istart irnp ipf ?Goal)
     hd ?Goal0 ?Goal1) = k
*)
Theorem dotadvancerXk: forall hd x k inn pt p0 p1 
  (prx:eitGetEndPos hd = x)
  (pnn: eitGetPending hd <> nil), 
eitGetEndPos (dotAdvancerN x k inn pt hd p0 p1) = k.
Proof.
  intros.
  destruct hd.
  simpl.
  destruct pnd.
  simpl in *.
  discriminate.
  simpl.
  simpl in prx.
  rewrite last_last.
  auto.
Qed.

(** A predictor továbbra is a megfelelő earley itemeket fogja létrehozni, de szolgáltatnia kell bizonyítékokat. A bizonyíték hogy az elemzett terminálisok vége a egfelelő helyen van egyszerű, hiszen a jelen setben kezdődik és a vége is itt ban mert még nem elemeztünk semmit. Az eddig lefedett terminálisok listéja az üreslista, mindenképpen része az eredeti listának. A bizonyítékot hogy a szabály része a nyelvtannak a gExtrRulD függvény szolgáltatja. Az üres szabályokat itt isfigyelembevesszük.

*)

Fixpoint predictorAux (k:nat) (n:N) (r:list({s: rule N T | s ∊ G} ))
    (s_curr:earleySetUnderConstruction k) : earleySetUnderConstruction k.
refine (
  match r with 
    | (exist _ head headProof) :: tail => 
    match (lhs head) =?= n with
      | left prf => predictorAux k n tail
            (insertIntoESC k s_curr
              (eiC n k nil nil (pfNil N T G i k) (rhs head) _ )
              eq_refl)
      | right prf => predictorAux k n tail s_curr
    end
    | nil => s_curr
  end
).
simpl.
rewrite <- prf.
rewrite ruleReassemble.
exact headProof.
Defined.

Fixpoint predictor (k:nat) (ei:earlyItemD)
    (s_curr:earleySetUnderConstruction k) (prf: eitGetEndPos ei = k):
      earleySetUnderConstruction k.
refine(
       match (getNextSymbolFromEarleyItem ei) as eii 
       return getNextSymbolFromEarleyItem ei = eii -> _  
       with
         | inleft (inl n) => fun heq =>
         let sNext := predictorAux k n
             (listToMembershipProofList (grammarGetRules G))
             s_curr in
         match isNullable n with
           | Just x => insertIntoESC k sNext
             (dotAdvancerN k k n
                 (x i k) ei heq prf) _ 
           | Nothing => sNext
         end
         | _ => fun heq => s_curr
       end eq_refl 
).
rewrite <- prf.
apply dotadvancerNul.
Defined.

(** A scannernek is nyújtania kell bizonyos bizonyítékokat. Bizonyatani kell hogy amikor a scanner előremozgatja a pontot egy itemben, az item által lefedett terminálisok listája egyel hosszabb lesz, az új elemmel együtt is része az eredeti terminálisok listájának, és a szabály továbbra is része a nyelvtannak. 

*)

Definition scanner (k:nat) (it:earlyItemD)
  (s_next:earleySetUnderConstruction (S k)) 
   (kOneAhead: (eitGetEndPos it) = k)
  : earleySetUnderConstruction (S k).
refine (
    match it as iit return it = iit -> _ 
    with eiC n start rns rnp pf pnd pM => fun ieq => 
      match pnd as remsymb return pnd = remsymb -> _ with 
      
      | cons (inr t) tl => fun heq =>
     match (AtPosDec t i k) with 
       | left p => 
         (insertIntoESC (S k) s_next (eiC n start (rns ++ [inr t])
         _ (ptSnocT _ _ _ i _  _  (S k) _ pf t _ _) tl _) _)
       | _ => s_next
     end
    | _ => fun heq => s_next
    end eq_refl
    end eq_refl
).
Unshelve.
simpl.
apply last_last.
rewrite ieq in kOneAhead.
simpl in kOneAhead.
lia.
rewrite ieq in kOneAhead.
simpl in kOneAhead.
rewrite kOneAhead.
exact p.
rewrite <- app_assoc.
simpl.
rewrite <- heq.
exact pM.
Defined.


(** A transferItems a lookup által visszaadott listának az elemeire meghívja a dotadvancert, és beírja őket a jelenlegi setbe. Ehez előállítjuk a bizonyítékot az insert függvény számára, hogy megfelelő helyen ér véget a lefedett terminálisok listája, ehez felhasználjuk a bemenetként megadott bizonyítékokat a befejezett szabály által lefedett szimbólumok kezdő és vég pontjára, illetve a dotadvancerXk tételt. A dotadvancernek szükséges bizonítékokat előállítjuk az itemben tárolt bizonyatékokból, és parsetreeeben térolt bizonyítékokat is, a befejezett earley itemben levő bizonyítékokkal, valamint inputként megkapjuk hogy a beffejezett szabály bal oldala megegyezik a B paraméterrel, és nincs több vizsgálatlan elem a szabályban.

*)

Fixpoint transferItems (x:nat) (k:nat) (B:N) (it:earlyItemD)
           (pendIsNull: eitGetPending it = nil)
           (beginIsX: eitGetStartposition it = x)
           (endIsK : eitGetEndPos it = k)
           (lhsIsB : lhs (eitGetRule it) = B)
           (source: list {it : earlyItemD |
               getNextSymbolFromEarleyItem it = inleft (inl B)
               /\  eitGetEndPos it = x} ) 
           (target: earleySetUnderConstruction k):
           earleySetUnderConstruction k.
refine(
match it as iit
return it = iit -> earleySetUnderConstruction k
with
  eiC inn istart irns irnp ipf ipnd ipM =>
   fun ieq =>
  match source as ssource return source = ssource -> _ with
    | nil => fun _ =>target
    | cons (exist _ hd prf) tl => fun seq =>
        transferItems  x k B it pendIsNull beginIsX endIsK lhsIsB tl
        (insertIntoESC k target 
          (
             dotAdvancerN x k inn
                (ptNode G i x k inn irns _ _ ipf _) hd _ _
          )
        _)
  end eq_refl
end eq_refl
).
apply (dotadvancerXk _ x k).
destruct prf as [prf1 prf2].
firstorder.
destruct hd.
destruct pnd;
cbn in prf |- *;
destruct prf;
congruence.
Unshelve.
rewrite ieq in pendIsNull.
cbn in pendIsNull.
rewrite  (app_nil_end irns).
rewrite <- pendIsNull.
exact ipM.

rewrite ieq in lhsIsB.
simpl in lhsIsB.
rewrite lhsIsB.
destruct prf as [prf1 prf2].
exact prf1.

destruct prf as [prf1 prf2].
exact prf2.
Defined.



(** A completernek nem sok feladata maradt, meghívja a lookup függvényt, majd az általa visszaadott értékkel, és további megfleleő paraméterekkel a transferItems függvényt. Ehhez a bizonyítékokat a kezdő pozícióra és a B paraméterre vonatkozókhoz elég egy egyszerű reflexivitási tétel, hiszen pont onnan olvastuk ki őket amivel meg kell egyeznie, a másik kettőt pedig beneő paraméterként fogja megkapni.

*)

Definition completer (k:nat) (it:earlyItemD)
   (s_completed: completedEarleySets)
   (s_curr:earleySetUnderConstruction k) 
   (pendIsNull: eitGetPending it = nil)
   (endPosIsK: eitGetEndPos it = k):
      earleySetUnderConstruction k.
refine(
  let source := lookup s_completed (lhs (eitGetRule it))
                       (eitGetStartposition it) in 
  transferItems (eitGetStartposition it) k (lhs (eitGetRule it)) 
  it pendIsNull eq_refl endPosIsK eq_refl source s_curr

).
Defined.


(** A findRules tovébbra is azokat a szabályokat keresi, aminek a kezdőszimbólum áll a bal oldalán. A gExtrRul függvény által visszaadott listának minden eleméhez tartozik egy bbizonyítás, hogy beletartozik a nyelvtanba. Mindig abba a felébe kell belenézni amiben a szabály van, de az eredmény listába a teljes elemeket kell beletenni.

*)
Definition findRules (n:N) : list {a : rule N T | In a (grammarGetRules G)}:= 
  let lp := (listToMembershipProofList (grammarGetRules G)) in 
  filter  (fun '(exist _ r _) => if nEq n (lhs r) then true else false ) lp.

(** A oneSet függvény nem sokat változott, az alapvető működése ugyanaz, de a meghívott fügvényekhez bizonyítékokat kell adn. A predictornak és a csannernek csak egy bizonyíték kell, a vizsgált earley item által lefedett terminálisok végéről, ezt ki tudjuk olvasni az itemből. A completernek ugyanez mellé kell mégegy bizonyíték, ami azt igazolja, hogy nincs több elem a vizsgálatra váró részében, ez a match-ből ered, abban az ágában hívjuk meg, amikor nem tudtunk beolvasni több elemet a listából.

*)

Fixpoint oneSet (k:nat)
  (s_completed: completedEarleySets)
  (s_curr:earleySetUnderConstruction k) 
  (s_next:earleySetUnderConstruction (S k))
  (num:nat): 
  completedEarleySets * earleySetUnderConstruction (S k).
refine(
  match num , getNextUnprocessed k s_curr with 
    | S x, Just (exist _ it prf) =>
    match getNextSymbolFromEarleyItem it with
      | inleft nt => 
      match nt with
        | inl n => oneSet k
           s_completed
          (markAsCompleted k (predictor k it s_curr prf))
          s_next x
        | inr t =>

          oneSet k s_completed
          (markAsCompleted k s_curr)
          (scanner k it s_next prf) 
          x
      end
      | inright heq =>
          oneSet k s_completed
          (markAsCompleted k (completer k it s_completed s_curr heq prf))
          s_next x
    end
    | _,_ => (s_completed++[(let (k0,A,_):= s_curr in existT _ k0 A)],s_next)
  end
).
Defined.


Fixpoint ParserAux 
  (k:nat)
  (s_completed: completedEarleySets)
  (s_curr:earleySetUnderConstruction k) 
  (s_next:earleySetUnderConstruction (S k))
  (lng fuel:nat):
  completedEarleySets:=
    match lng with 
      | S x => 
          match (oneSet k s_completed 
          s_curr s_next fuel) with
            | (a,b) => ParserAux (S k) a b
                              (sucC (S (S k)) nil nil) x fuel
          end
      |_ => s_completed
  end.

(**Az isNil megállapítja, hogy a megadott lista üres-e. A visszatérési érték sumbool.

*)

Definition isNil {A:Type} (a:list A): {a = nil}+{a <> nil}.
refine(
  match a as aa return {aa = nil}+{aa <> nil} with 
    | nil => left eq_refl
    | _ => right _
  end
).
discriminate.
Defined.

(** A proofFilter a filterhez hasonlóan működik, szüksége van bemeneti paraméterként egy listára és egy függvényre amit a lista elemeire meghívva egy sumbool értéket ad vissza. Amire az érték igaz, azt beletesszük a visszatérési listába, a sumboolban levő bizonyítékkal együtt.

*)

Fixpoint proofFilter {A:Type} {P Q : A -> Prop} (f: forall a:A , {P a} + {Q a}) (l: list A): list {a:A | P a}:=
  match l with
    | nil => nil
    | cons hd tl => 
      match (f hd) with 
         | left p => exist _ hd p :: (proofFilter f tl) 
         | _ => (proofFilter f tl)
      end
    end.

(** A makeces függvény egy új függvény, ez fogha a parserAuxot meghívni, ez állítja elő a teljes befejezett earley seteket. A makeces állítja itt elő a szükséges üres setek listáját, meghívja a findrulest, és a visszaadott szabályokhoz earley itemeket csinál, üres parseforestekkel, és bizonyításokkal. A bizonyítások egyszerüek, minden feldolgozott terminális lista üres, tehét az eleje és a vége is 0, a szabály nyelvtanbatartozását pedig bizonyítja a findRules függvény.

*)

Definition makeCes (fuel:nat): completedEarleySets.
refine (

  ParserAux 0 nil 
    (sucC O nil 
        (map (fun '(exist _ r p) => exist _ 
    (eiC (lhs r) 0 nil nil (pfNil N T G i 0) (rhs r) _) _)
        (findRules (grammarGetStart G)))
    )
    (sucC 1 nil nil) (length i+1) fuel
).
simpl.
reflexivity.
Unshelve.
simpl.
cbn in p.
rewrite ruleReassemble.
exact p.
Defined.


(** A parser függvény meghívja a makeCes függvényt, majd az utolsó setből kiválasztja az early itemet ami megfelel a hátom kritériumnak, a proofFilterrel. A szabály végén van a pont, erre használjuk az isNil függvényt, a kezdőszimbólum a baloldala, és az nulladik setben kezdődött. Ha nem találunk ilyen semmti adunk vissza, ha találunk ilyeneket, akkor az elsőt, kiválasztjuk és visszaadjuk parseTreeDepWithInput-ot.

*)

Definition Parser 
  (fuel:nat): Maybe (parseTreeDep N T G i 0 (length i) (grammarGetStart G)).
refine(
  let ces := makeCes fuel
    in let finalItemE := getKfromCes (length i) ces in 
    
    let ptree := proofFilter (fun it => 
      sumbool_and _ _ _ _ (sumbool_and _ _ _ _ (nEq (lhs (eitGetRule (proj1_sig it))) (grammarGetStart G) ) 

      (isNil (eitGetPending (proj1_sig it)))) 
      (Nat.eq_dec (eitGetStartposition (proj1_sig it)) O)) finalItemE 
    in match ptree with
         | nil => Nothing
         | cons (exist _ hd hdprf) _ => 
         match hd as hhd return hd = hhd -> _ with
           | exist _ e prf => fun hdeq =>
           match e as ee return e = ee -> _ with
             |eiC n bpos rns rnp pf pnd pM => fun heq => Just _ 
           end eq_refl
         end eq_refl
       end

).
clear ptree.


rewrite hdeq in hdprf.
simpl in hdprf.
clear hdeq.
rewrite heq in prf.
simpl in prf.
rewrite heq in hdprf.
simpl in hdprf.
destruct hdprf as [[hdprf1 hdprf2] hdprf3].
clear heq.
eapply ptNode.
apply pf.
rewrite hdprf2 in pM.
rewrite <- app_nil_end in pM.
rewrite <- hdprf1.
apply pM.
Defined.


End Earleycontext.

Print Assumptions Parser.
(*Arguments eitGetRule [N T] _.
Arguments eitGetPOD [N T] _.
Arguments eitExtrSP [N T] _.
Arguments getNextUnprocessed [N T] _.
Arguments insertIntoESC [N T] _ _ _ _.
Arguments getNextSymbolFromEarleyItem [N T] _.
Arguments predictor [N T] _ _ _ _ _ _.
Arguments scanner [N T] _ _ _ _ _ _.
*)
