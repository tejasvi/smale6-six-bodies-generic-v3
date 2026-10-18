import L6SoundK.F1.Sort
import L6Sound.F1.Complete
import L6K.F1.Shard

/-!
# The search of Proposition 3.1 is the union of its shards

`edgeLeaves 6` is the union, over the prefixes `p ∈ edgesUpTo 6 m`, of the extensions `extendFrom m p`; so `search 6`
is the union of the diagrams found in the shards. Leaves of different prefixes are different (an extension keeps the
digits already set).
-/

namespace L6K.F1

open L6F1

/-- The steps `m, …, m + k - 1` of the edge stage. -/
def ext (m k : ℕ) (L : List ℕ) : List ℕ := (List.range k).foldl (fun L j => extendAt 6 (m + j) L) L

theorem ext_succ (m k : ℕ) (L : List ℕ) : ext m (k + 1) L = extendAt 6 (m + k) (ext m k L) := by
  unfold ext
  rw [List.range_succ, List.foldl_append]
  rfl

theorem extendAt_flatMap (j : ℕ) (L : List ℕ) (f : ℕ → List ℕ) :
    extendAt 6 j (L.flatMap f) = L.flatMap fun x => extendAt 6 j (f x) := by
  unfold extendAt
  simp only [List.flatMap_assoc]

theorem ext_eq_flatMap (m : ℕ) : ∀ (k : ℕ) (L : List ℕ), ext m k L = L.flatMap fun p => ext m k [p]
  | 0, L => by simp [ext]
  | k + 1, L => by
    rw [ext_succ, ext_eq_flatMap m k L, extendAt_flatMap]
    simp only [ext_succ]

theorem edgesUpTo_add (m : ℕ) : ∀ k, edgesUpTo 6 (m + k) = ext m k (edgesUpTo 6 m)
  | 0 => by simp [ext]
  | k + 1 => by
    rw [ext_succ, ← edgesUpTo_add m k, ← Nat.add_assoc]
    rfl

theorem extendFrom_eq (m p : ℕ) : extendFrom m p = ext m (15 - m) [p] := rfl

/-- **The edge stage in shards** (prefixes of `m ≤ 15` positions). -/
theorem edgeLeaves_eq {m : ℕ} (hm : m ≤ 15) : edgeLeaves 6 = (edgesUpTo 6 m).flatMap (extendFrom m) := by
  have h : edgeLeaves 6 = edgesUpTo 6 (m + (15 - m)) := by
    rw [Nat.add_sub_cancel' hm]; rfl
  rw [h, edgesUpTo_add, ext_eq_flatMap]
  rfl

/-- **The search in shards.** -/
theorem search_eq {m : ℕ} (hm : m ≤ 15) :
    L6F1.search 6 = (edgesUpTo 6 m).flatMap fun p => searchFrom 6 (extendFrom m p) := by
  unfold L6F1.search searchFrom
  rw [edgeLeaves_eq hm, List.flatMap_assoc]

/-! ## Extensions keep the digits already set -/

theorem mem_extendAt {j e : ℕ} {L : List ℕ} (h : e ∈ extendAt 6 j L) : ∃ x ∈ L, ∃ v < 4, e = x + v * 4 ^ j := by
  unfold extendAt at h
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_cons, List.not_mem_nil] at h
  obtain ⟨x, hx, ⟨v, hv, rfl⟩, -⟩ := h
  refine ⟨x, hx, v, ?_, rfl⟩
  rcases hv with rfl | rfl | rfl | rfl | h <;> simp_all

theorem mod_of_mem_ext (m : ℕ) : ∀ (k : ℕ) {e p : ℕ}, e ∈ ext m k [p] → e % 4 ^ m = p % 4 ^ m
  | 0, e, p, h => by simp [ext] at h; rw [h]
  | k + 1, e, p, h => by
    rw [ext_succ] at h
    obtain ⟨x, hx, v, _, rfl⟩ := mem_extendAt h
    rw [← mod_of_mem_ext m k hx]
    obtain ⟨c, hc⟩ : 4 ^ m ∣ v * 4 ^ (m + k) := Dvd.dvd.mul_left (pow_dvd_pow 4 (Nat.le_add_right m k)) v
    rw [hc, Nat.add_mul_mod_self_left]

theorem lt_of_mem_edgesUpTo : ∀ (j : ℕ) {p : ℕ}, p ∈ edgesUpTo 6 j → p < 4 ^ j
  | 0, p, h => by simp [edgesUpTo] at h; subst h; norm_num
  | j + 1, p, h => by
    obtain ⟨x, hx, v, hv, rfl⟩ := mem_extendAt h
    have := lt_of_mem_edgesUpTo j hx
    rw [pow_succ]
    nlinarith

theorem mod_of_mem_extendFrom {m e p : ℕ} (hp : p ∈ edgesUpTo 6 m) (he : e ∈ extendFrom m p) :
    e % 4 ^ m = p := by
  rw [extendFrom_eq] at he
  rw [mod_of_mem_ext m (15 - m) he, Nat.mod_eq_of_lt (lt_of_mem_edgesUpTo m hp)]

end L6K.F1
