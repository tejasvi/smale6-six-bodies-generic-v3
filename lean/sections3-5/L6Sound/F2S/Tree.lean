import L6Sound.F2S.TreeAux2
import L6Sound.F2S.TreeAux3

/-!
# Trees of the specification search: restriction and insertion

For a complete tree with heights `X` (`ExpTree.Good`):

* `restrict_init`: restricted to `{O}` it is the tree of the search's start;
* `options_complete`: the restriction to `S ∪ {p}` is, up to the order of the nodes, one of the insertions of `p` into
  any tree equivalent to the restriction to `S` (the proof of Proposition 4.5: "restricting two trees to fewer points
  gives partial trees visited by the search");
* `restrict_all`: restricted to all seven points it is itself;
* `levelFacts`: a tree equivalent to the restriction to `S` has the facts that its rows use (`LevelFacts`);
* `comOk_equiv`, `key_equiv`: the root rule and the key depend only on the nodes as a set.

Here `S` is a set of points containing `O` (a prefix of the insertion order), and `p` a body not in `S`.
-/

namespace L6.F2S

variable {X : ExpTree}

theorem restrict_init (hX : X.Good) : TS.init.Equiv (restrict X.T (single O)) :=
  TreeAux.restrict_init' hX

theorem options_complete (hX : X.Good) {S p : Nat} (hS : S < 128) (hO : mem O S = true) (hp : p < 6)
    (hpS : mem p S = false) {T : TS} (hT : T.Equiv (restrict X.T S)) (hTn : T.nodes.Nodup) :
    ∃ T' ∈ T.options S p, T'.Equiv (restrict X.T (ins p S)) ∧ T'.nodes.Nodup :=
  TreeAux.options_complete' hX hS hO hp hpS hT hTn

theorem restrict_all (hX : X.Good) : (restrict X.T all).Equiv X.T :=
  TreeAux.restrict_all' hX

theorem levelFacts (hX : X.Good) (hroot : -2 ≤ X.h all) {S : Nat} (hS : S < 128) (hO : mem O S = true) {T : TS}
    (hT : T.Equiv (restrict X.T S)) (hTn : T.nodes.Nodup) : LevelFacts X T S :=
  TreeAux.levelFacts' hX hroot hS hO hT hTn

theorem comOk_equiv {T T' : TS} (h : T.Equiv T') (hn : T.nodes.Nodup) (hn' : T'.nodes.Nodup) (S : Nat) :
    comOk T S = comOk T' S :=
  TreeAux.comOk_equiv' h hn hn' S

theorem key_equiv {T T' : TS} (h : T.Equiv T') (hn : T.nodes.Nodup) (hn' : T'.nodes.Nodup) : T.key = T'.key :=
  TreeAux.key_equiv' h hn hn'

theorem TS.Equiv.symm {T T' : TS} (h : T.Equiv T') : T'.Equiv T := ⟨h.1.symm, h.2.symm⟩

theorem TS.Equiv.trans {T T' T'' : TS} (h : T.Equiv T') (h' : T'.Equiv T'') : T.Equiv T'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

end L6.F2S
