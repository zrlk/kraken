/-
The environment state of `SharedEnv.lastWrite` as a Promising memory: the
ISA-free part of the link (design note
`Kraken/Promising/EnvWP.md` §8). Shared by x64 (`Kraken.Promising.EnvWPX64`)
and AArch64 (`Kraken.Promising.EnvWPAArch64`); both ISAs' merged links use the
same `MemRel` and `sharedBytes` (`Kraken.Promising.MergedMem`).

- `envRel L g mem`: the environment state `g` holds the last write to every
  shared location of `mem`.
- `MergeRel L d g D`: `MemRel` with the environment state in place of the
  Promising memory.
- `gmem L g`: a message-free memory with initial values `g` on `L`, so
  `MergeRel L d g D` is `MemRel L d (gmem L g) D` (`mergeRel_iff`) and the
  lemmas of `Kraken.Promising.MergedMem` serve the environment state.
- `memRel_iff_mergeRel_of_envRel`, `exists_merge`: the two facts the
  `EnvLinkHalt` proofs use at the start and at the end of a run.

Everything here mentions the Promising memory only through `envRel` and
`gmem`, so a change of `Val`/`Loc` touches those and nothing else.
-/
import Kraken.SharedEnv
import Kraken.Promising.MergedMem

open Kraken

namespace Kraken.Promising

/-! ## Relating the environment state to the merged memory -/

/-- The environment state `g` of `lastWrite L` holds the last write to every
shared location of `mem`, at the location's width. -/
def envRel (L : SharedLayout) (g : BitVec 64 → BitVec 128) (mem : Memory) : Prop :=
  ∀ a n, (a, n) ∈ L → (g a).setWidth (8 * n) = (mem.finalVal (sharedLoc a n)).setWidth (8 * n)

/-- The merged memory `D` of the private memory `d` and the environment state
`g`: `MemRel` with the environment state in place of the Promising memory. -/
structure MergeRel (L : SharedLayout) (d : Mem 64) (g : BitVec 64 → BitVec 128) (D : Mem 64) :
    Prop where
  priv : ∀ k, ¬ L.Covers k → D.get? k = d.get? k
  split : ∀ k, L.Covers k → d.get? k = none
  shared : ∀ a n, (a, n) ∈ L → D.loadBytes a n = some (Int.toBytes n ((g a).toNat : Int))

/-! ## The environment state as a Promising memory

`gmem L g` is a memory without messages whose initial values are `g` on the
locations of `L`. `MergeRel L d g D` is `MemRel L d (gmem L g) D`
(`mergeRel_iff`), so the lemmas of `Kraken.Promising.MergedMem` serve the
environment state as they serve the Promising memory. -/

/-- A memory without messages holding `g a` at every location `(a, n)` of `L`. -/
def gmem (L : SharedLayout) (g : BitVec 64 → BitVec 128) : Memory :=
  { init := L.map fun p => (sharedLoc p.1 p.2, g p.1), msgs := #[] }

theorem gmem_finalVal {L : SharedLayout} {g : BitVec 64 → BitVec 128} {a : BitVec 64} {n : Nat}
    (h : (a, n) ∈ L) : (gmem L g).finalVal (sharedLoc a n) = g a := by
  have hs : ((L.map fun p => (sharedLoc p.1 p.2, g p.1)).find? (·.1 == sharedLoc a n)).isSome :=
    List.find?_isSome.mpr ⟨_, List.mem_map_of_mem h, by simp⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
  have hq1 := List.find?_some hq
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hq)
  have hpa : p.1 = a := by
    simp only [beq_iff_eq] at hq1
    exact congrArg Loc.addr hq1
  simp only [Memory.finalVal, gmem, Memory.initVal]
  rw [show (#[] : Array Msg).findRev? (·.loc == sharedLoc a n) = none from rfl]
  simp only [hq, Option.map_some, Option.getD_some, hpa]

/-- `MemRel` only reads the memory at the locations of the layout. -/
theorem MemRel.congr {L : SharedLayout} {d D : Mem 64} {m m' : Memory} (h : MemRel L d m D)
    (hm : ∀ a n, (a, n) ∈ L → m'.finalVal (sharedLoc a n) = m.finalVal (sharedLoc a n)) :
    MemRel L d m' D :=
  ⟨h.priv, h.split, fun a n ha => by rw [h.shared a n ha, sharedBytes, sharedBytes, hm a n ha]⟩

theorem mergeRel_iff {L : SharedLayout} {d D : Mem 64} {g : BitVec 64 → BitVec 128} :
    MergeRel L d g D ↔ MemRel L d (gmem L g) D := by
  constructor
  · intro h
    exact ⟨h.priv, h.split, fun a n ha => by rw [h.shared a n ha, sharedBytes, gmem_finalVal ha]⟩
  · intro h
    exact ⟨h.priv, h.split, fun a n ha => by rw [h.shared a n ha, sharedBytes, gmem_finalVal ha]⟩

/-- A store of `v` to the shared location `(a, n)`: the merged memory takes it,
and the environment state is updated at `a` with `v` zero-extended. -/
theorem MemRel.store_gmem {L : SharedLayout} (hL : L.WF) {d D : Mem 64} {g : BitVec 64 → BitVec 128}
    (h : MemRel L d (gmem L g) D) {a : BitVec 64} {n w : Nat} (ha : (a, n) ∈ L) (hw : w = 8 * n)
    (v : BitVec w) :
    MemRel L d (gmem L (SharedEnv.upd g a (v.setWidth 128))) (Mem.storeInt D a n v.toInt) := by
  refine (h.store_shared hL ha hw v 0).congr fun b m hb => ?_
  rw [gmem_finalVal hb, Memory.finalVal_append, SharedEnv.upd]
  by_cases hab : b = a
  · subst hab
    have hmn : m = n := (hL.disj b m b n b hb ha (by simp [hL.pos b m hb]) (by simp [hL.pos b n ha])).2
    subst hmn
    simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hab),
      ite_eq_right_of_eq_false _ _ (eq_false fun he => hab (congrArg Loc.addr he).symm), gmem_finalVal hb]

/-- The value of a shared location read from the merged memory, at the access
width, is the environment state's. -/
theorem MemRel.loadInt_gmem {L : SharedLayout} {d D : Mem 64} {g : BitVec 64 → BitVec 128}
    (h : MemRel L d (gmem L g) D) {a : BitVec 64} {n : Nat} (ha : (a, n) ∈ L) :
    Mem.loadInt D a n = some (Int.ofBytes (sharedBytes (gmem L g) a n)) := by
  unfold Mem.loadInt
  rw [h.shared a n ha]
  rfl

theorem sharedBytes_gmem {L : SharedLayout} {g : BitVec 64 → BitVec 128} {a : BitVec 64} {n w : Nat}
    (ha : (a, n) ∈ L) (hw : w = 8 * n) :
    BitVec.ofInt w (Int.ofBytes (sharedBytes (gmem L g) a n)) = (g a).setWidth w := by
  rw [sharedBytes_val _ a hw, gmem_finalVal ha]

/-- An access the private memory serves misses the footprint. -/
theorem MemRel.ok_of_loadBytes {L : SharedLayout} {d D : Mem 64} {m : Memory} (h : MemRel L d m D)
    {a : BitVec 64} {n : Nat} (hd : (d.loadBytes a n).isSome) : ∀ i < n, ¬ L.Covers (a + BitVec.ofNat 64 i) := by
  intro i hi hc
  have := Mem.get?_isSome_of_loadBytes hd i hi
  rw [h.split _ hc] at this
  cases this

theorem MemRel.ok_of_loadInt {L : SharedLayout} {d D : Mem 64} {m : Memory} (h : MemRel L d m D)
    {a : BitVec 64} {n : Nat} {x : Int} (hd : Mem.loadInt d a n = some x) : L.Ok a n :=
  .inr (h.ok_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hd))

/-! ## Agreement at a width, and the merge of a start state -/

/-- The bytes of two values agree exactly when the values agree at the width. -/
theorem toBytes_eq_iff {n : Nat} {x y : BitVec 128} :
    Int.toBytes n (x.toNat : Int) = Int.toBytes n (y.toNat : Int) ↔ x.setWidth (8 * n) = y.setWidth (8 * n) := by
  have key : ∀ x : BitVec 128, BitVec.ofInt (8 * n) (Int.ofBytes (Int.toBytes n (x.toNat : Int))) =
      x.setWidth (8 * n) := fun x => by
    rw [BitVec.ofInt_ofBytes_toBytes_eq _ n rfl, BitVec.ofInt_natCast]
    exact BitVec.ofNat_toNat _ _
  refine ⟨fun h => by rw [← key x, ← key y, h], fun h => ?_⟩
  rw [← Int.toBytes_emod n (x.toNat : Int), ← Int.toBytes_emod n (y.toNat : Int), Int.take, Int.take]
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have h2 : (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) := by rw [Int.natCast_pow]; rfl
  rw [h2, ← Int.natCast_emod, ← Int.natCast_emod, this]

/-- `MemRel` is `MergeRel` at any environment state related to the memory. -/
theorem memRel_iff_mergeRel_of_envRel {L : SharedLayout} {d D : Mem 64} {mem : Memory}
    {g : BitVec 64 → BitVec 128} (henv : envRel L g mem) : MemRel L d mem D ↔ MergeRel L d g D := by
  rw [mergeRel_iff]
  have hb : ∀ a n, (a, n) ∈ L → sharedBytes mem a n = sharedBytes (gmem L g) a n := fun a n ha => by
    rw [sharedBytes, sharedBytes, gmem_finalVal ha, toBytes_eq_iff.mpr (henv a n ha).symm]
  exact ⟨fun h => ⟨h.priv, h.split, fun a n ha => by rw [h.shared a n ha, hb a n ha]⟩,
    fun h => ⟨h.priv, h.split, fun a n ha => by rw [h.shared a n ha, hb a n ha]⟩⟩

/-- A merged memory exists: store every shared location's value over the
private memory. -/
theorem exists_merge {L : SharedLayout} (hL : L.WF) (g : BitVec 64 → BitVec 128) (d : Mem 64) :
    ∀ M : SharedLayout, (∀ p ∈ M, p ∈ L) →
      ∃ D : Mem 64, (∀ k, ¬ M.Covers k → D.get? k = d.get? k) ∧
        ∀ a n, (a, n) ∈ M → D.loadBytes a n = some (Int.toBytes n ((g a).toNat : Int))
  | [], _ => ⟨d, fun _ _ => rfl, fun _ _ h => nomatch h⟩
  | (a, n) :: M, hM => by
    obtain ⟨D, hpriv, hsh⟩ := exists_merge hL g d M fun p hp => hM p (List.mem_cons_of_mem _ hp)
    have haL : (a, n) ∈ L := hM _ List.mem_cons_self
    have hn := hL.le16 a n haL
    have h16 : (16 : Nat) < 2 ^ 64 := by decide
    have hlen : (Int.toBytes n ((g a).toNat : Int)).length = n := Int.toBytes_length _ _
    -- a byte the store writes is in `(a, n)`'s footprint
    have hin : ∀ k, k ∈ (Int.toBytes n ((g a).toNat : Int)).At a → (k - a).toNat < n := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ a k).mp hk
      rw [hlen] at hi
      rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hi
    have hhead : (D.storeBytes a (Int.toBytes n ((g a).toNat : Int))).loadBytes a n =
        some (Int.toBytes n ((g a).toNat : Int)) := by
      have := Mem.loadBytes_storeBytes D a (Int.toBytes n ((g a).toNat : Int)) (by rw [hlen]; omega)
      rwa [hlen] at this
    refine ⟨D.storeBytes a (Int.toBytes n ((g a).toNat : Int)), fun k hk => ?_, fun b m hb => ?_⟩
    · rw [Mem.get?_storeBytes_of_not_mem _ _ _ _ fun hk' => hk ⟨a, n, List.mem_cons_self, hin k hk'⟩]
      exact hpriv k fun ⟨b, m, hb, hkb⟩ => hk ⟨b, m, List.mem_cons_of_mem _ hb, hkb⟩
    · by_cases hab : b = a ∧ m = n
      · obtain ⟨rfl, rfl⟩ := hab
        exact hhead
      · have hb' : (b, m) ∈ M := by
          rcases List.mem_cons.mp hb with hb | hb
          · exact absurd (Prod.mk.inj hb) hab
          · exact hb
        rw [← hsh b m hb']
        apply Mem.loadBytes_congr
        intro i hi
        apply Mem.get?_storeBytes_of_not_mem
        intro hk
        have hbL := hM _ (List.mem_cons_of_mem _ hb')
        have hm := hL.le16 b m hbL
        obtain ⟨h1, h2⟩ := hL.disj a n b m _ haL hbL (hin _ hk) (by
          rw [BitVec.add_comm b, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact hi)
        exact hab ⟨h1.symm, h2.symm⟩

end Kraken.Promising
