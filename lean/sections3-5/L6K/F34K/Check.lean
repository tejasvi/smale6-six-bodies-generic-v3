import L6F34S.Check
import L6K.F2S.KeepR
import L6K.F2S.SearchRL

/-!
# The claims of Proposition 5.3 at the cells of the specification search, for the kernel

The checks of `L6F34S.Check` (`checkSingleS`, `constantArgminS`, `genForS`, `checkLinkS`) arranged for evaluation in
the kernel, on the rows of a cell of the search:

* each linear program `Π + {r}` is decided by a given certificate (`prunedK`: `checkR` on the rows with `r` last)
  instead of the floating-point simplex of `prunedWith`;
* the argmin set of an item of a core is given (`ItemK.S`) instead of guessed at a floating-point interior point; it
  is certified constant on the cell as in `constantArgminS`;
* polynomials are normalized with a merge sort written with the recursors (`normalizeK`): `L6.Poly.normalize` sorts
  with `List.mergeSort`, which the kernel does not unfold; both have the value of their input (`eval`);
* the name of an item is an `IdName`, the variables of a core are `VarM`s and the engine trees are `ETree`s, as data;
  a core's certificate is the entry `j` of a list of certificates.

`L6SoundK.F34K.Meaning` proves that a passing claim gives `ClaimMeaning` (`claimK_meaning`).
-/

namespace L6K.F34K

open L6 L6.F2S L6.F34S L6.Poly
open L6.F34 (Lab IdName)
open L6K.F2S (checkR)

noncomputable section

/-! ## A merge sort of polynomials, for the kernel -/

/-- Merge of two lists of terms by key (fuel: at least the total length). -/
def mergeP : Nat → Poly → Poly → Poly :=
  Nat.rec (motive := fun _ => Poly → Poly → Poly)
    (fun a b => a ++ b)
    (fun _ ih a b =>
      List.rec (motive := fun _ => Poly) b
        (fun x a' _ =>
          List.rec (motive := fun _ => Poly) a
            (fun y b' _ => Bool.rec (y :: ih a b') (x :: ih a' b) (Nat.ble x.1 y.1)) b)
        a)

/-- Merge sort of terms by key with fuel `d` for the depth. -/
def msortP : Nat → Poly → Poly :=
  Nat.rec (motive := fun _ => Poly → Poly)
    (fun l => l)
    (fun _ ih l =>
      List.rec (motive := fun _ => Poly) []
        (fun x t _ =>
          List.rec (motive := fun _ => Poly) [x]
            (fun _ _ _ => mergeP l.length (ih (l.take (l.length / 2))) (ih (l.drop (l.length / 2)))) t)
        l)

/-- The normal form for the kernel: sorted by key, equal keys merged, no zero coefficient. -/
def normalizeK (p : Poly) : Poly := combineSorted (msortP 40 p)

/-- `UPoly.pack` with `normalizeK`. -/
def packK (p : UPoly) : Poly := normalizeK (p.map fun a => (packExp a.2, a.1))

/-- `itemPoly` with `normalizeK`. -/
def itemPolyK (x : PCtx) (I : XId) (S : List Nat) (fixed : Int) : Option Poly :=
  match itemU x I S fixed with
  | none => none
  | some u => if u.small (6 + x.vars.size) then some (normalizeK (halve (packK u)).1) else none

/-- `distPoly` with `normalizeK`. -/
def distPolyK (x : PCtx) (k l : Nat) : Option Poly :=
  match dU x (k, l), lcU x true (k, l), lcU x false (k, l) with
  | some d, some a, some b =>
    if (distU d a b).small (6 + x.vars.size) then some (packK (distU d a b)) else none
  | _, _, _ => none

/-! ## Certified decisions -/

/-- The system `Π` plus the row `r` (last) has the certificate `cert`. -/
def prunedK (nh : Nat) (rows : Array Row) (r : Row) (cert : List (Nat × Int)) : Bool :=
  checkR nh (rows.toList ++ [r]) cert

/-- `strictlyLeastS` with the certificate of term `k` at position `k` of `certs`. -/
def strictlyLeastK (nv : Nat) (rows : Array Row) (fs : List (Option (Array Int))) (i : Nat)
    (certs : List (List (Nat × Int))) : Bool :=
  match fs.getD i none with
  | none => false
  | some fi =>
    (List.range fs.length).all fun k =>
      k == i ||
      match fs.getD k none with
      | none => true
      | some fk => prunedK nv rows (rowLe fk fi) (certs.getD k [])

/-- `constantArgminS` with the certificates of term `k` at position `k` of `cA` (the row `e_k ≥ e_{i₀} + s`, or
`e_k ≤ e_{i₀}` for `k ∉ S`) and of `cB` (the row `e_{i₀} ≥ e_k + s`). -/
def constantArgminK (nv : Nat) (rows : Array Row) (fs : List (Option (Array Int))) (S : List Nat)
    (cA cB : List (List (Nat × Int))) : Bool :=
  match S with
  | [] => false
  | i0 :: _ =>
    match fs.getD i0 none with
    | none => false
    | some f0 =>
      S.all (· < fs.length) &&
      (List.range fs.length).all fun k =>
        k == i0 ||
        match fs.getD k none with
        | none => !S.contains k
        | some fk =>
          if S.contains k then
            prunedK nv rows (rowGeS fk f0) (cA.getD k []) && prunedK nv rows (rowGeS f0 fk) (cB.getD k [])
          else prunedK nv rows (rowLe fk f0) (cA.getD k [])

/-- F3 for one cell (`checkSingleS` with certificates). -/
def checkSingleK (P : Pair) (rows : Array Row) (nm : IdName) (lab : Lab) (certs : List (List (Nat × Int))) : Bool :=
  match XId.ofName nm with
  | none => false
  | some I =>
    I.good &&
    match findLabX I.terms lab with
    | none => false
    | some i => strictlyLeastK P.nv rows (I.terms.map (termForm P)) i certs

/-! ## Cores -/

/-- An item of a core: its name, its argmin set and the certificates of its constancy. -/
structure ItemK where
  nm : IdName
  S : List Nat
  cA : List (List (Nat × Int))
  cB : List (List (Nat × Int))
  deriving Inhabited

/-- `genItem` with the given argmin set. -/
def genItemK (x : PCtx) (rows : Array Row) (fixed : Int) (it : ItemK) : Option Poly :=
  match XId.ofName it.nm with
  | none => none
  | some I =>
    if I.good then
      if constantArgminK x.P.nv rows (I.terms.map (termForm x.P)) it.S it.cA it.cB then itemPolyK x I it.S fixed
      else none
    else none

/-- `genForS` on an item. -/
def genForSK (x : PCtx) (rows : Array Row) (fixed : Int) (it : ItemK) : Option Poly :=
  match it.nm with
  | .dist k l => if k < l && l < 6 then distPolyK x k l else none
  | _ => genItemK x rows fixed it

/-- F4 for one cell (`checkLinkS` on items): the certificate has the variables and the fixed mass of the core, and
each generator is the certified initial form of its item. -/
def checkLinkK (x : PCtx) (rows : Array Row) (fixed : Int) (items : List ItemK) (cert : Cert) : Bool :=
  cert.nvar == x.vars.size && cert.fixed == fixed && decide (fixed < 6) && cert.gens.length == items.length &&
  (List.range items.length).all fun i => genForSK x rows fixed (items.getD i default) == some (normalizeK cert.gens[i]!)

/-! ## The claim of a cell -/

/-- The claim of a cell: a single term, or a core with the index of its certificate, its fixed mass, its variables,
the engine trees and its items. -/
inductive ClaimK where
  | single (nm : IdName) (lab : Lab) (certs : List (List (Nat × Int)))
  | core (cert : Nat) (fixed : Int) (vars : Array VarM) (ez ew : ETree) (items : List ItemK)

/-- The part of a certificate that the link of a core reads: its number of variables, fixed mass and generators. -/
abbrev CertKey := Nat × Int × List Poly

/-- **The check of a claim** on the pair `P` with the rows `rows` of its cell (`certs`: the keys of the certificates
of the cores). -/
def claimK (certs : List CertKey) (P : Pair) (rows : Array Row) : ClaimK → Bool
  | .single nm lab cs => checkSingleK P rows nm lab cs
  | .core j fixed vars ez ew items =>
    match certs[j]? with
    | none => false
    | some g => checkLinkK { P, ez, ew, vars } rows fixed items ⟨g.1, g.2.1, g.2.2, [], []⟩

/-- The claims of the cells, in order (as many claims as cells). -/
def checkCells (certs : List CertKey) : List L6K.F2S.RCell → List ClaimK → Bool
  | [], [] => true
  | c :: cs, k :: ks => claimK certs ⟨c.tz, c.tw⟩ (Array.mk c.rows) k && checkCells certs cs ks
  | _, _ => false

end

end L6K.F34K
