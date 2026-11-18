import Kraken.X64.Examples.Sbr.SessionBin.WitLeafBasic
import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# The witness stand-ins: `memset`

The byte loop `memsetT` meets `memset`'s value contract `Parse.MemsetValSpec`: the old bytes of
`dst[n]` are a logical variable (`memset_pair`); the loop invariant is that the first `rcx` of
them are the fill byte (`fillL`).
-/

open Kraken.X64.Parser Kraken Kraken.SysV Std.WP Mem MachineWP
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.WitEnv

/-- The first `i` bytes of `old` set to `b`. -/
def fillL (b : UInt8) (old : List UInt8) (i : Nat) : List UInt8 :=
  List.replicate i b ++ old.drop i

theorem fillL_length (b : UInt8) (old : List UInt8) (i : Nat) (h : i ≤ old.length) :
    (fillL b old i).length = old.length := by
  simp only [fillL, List.length_append, List.length_replicate, List.length_drop]; omega

theorem fillL_succ (b : UInt8) (old : List UInt8) (i : Nat) (_h : i < old.length) :
    (fillL b old i).take i ++ [b] ++ (fillL b old i).drop (i + 1) = fillL b old (i + 1) := by
  have h1 : (fillL b old i).take i = List.replicate i b := by
    simp [fillL]
  have h2 : (fillL b old i).drop (i + 1) = old.drop (i + 1) := by
    simp only [fillL, List.drop_append, List.length_replicate, List.drop_replicate,
      Nat.sub_eq_zero_of_le (Nat.le_succ i), List.replicate_zero, List.nil_append,
      List.drop_drop, show i + 1 - i = 1 by omega]
  rw [h1, h2, fillL, List.replicate_succ', List.append_assoc]

theorem fillL_full (b : UInt8) (old : List UInt8) :
    fillL b old old.length = List.replicate old.length b := by
  simp [fillL]

theorem tb1 (v : BitVec 8) : Int.toBytes 1 v.toInt = [UInt8.ofBitVec v] := by
  revert v; decide

/-- A byte store at offset `i` of a filled cell fills one more byte. -/
theorem fill_store {m : Mem 64} {b : UInt8} {old : List UInt8} {i : Nat} {a : BitVec 64}
    {K : Mem 64 → Prop} (hm : m =⋆ fillL b old i =@ a ⋆ K) (hi : i < old.length)
    (hw : old.length < 2 ^ 64) (a' : BitVec 64) (ha : a' = a + BitVec.ofNat 64 i) (v : BitVec 8)
    (hv : UInt8.ofBitVec v = b) :
    m.storeInt a' 1 v.toInt =⋆ fillL b old (i + 1) =@ a ⋆ K := by
  have hl := fillL_length b old i (by omega)
  have hoff : (a' - a).toNat = i := by
    rw [ha, show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega,
      BitVec.toNat_ofNat]; omega
  have := Val.storeInt_slice_split (n := 1) hm (Split.here _ _) (by rw [hoff, hl]; omega)
    (by rw [hl]; omega) v.toInt
  rw [hoff, tb1, hv, fillL_succ b old i hi] at this
  exact this

/-- A byte load at offset `i` of a filled cell is defined. -/
theorem fill_load {m : Mem 64} {b : UInt8} {old : List UInt8} {i : Nat} {a : BitVec 64}
    {K : Mem 64 → Prop} (hm : m =⋆ fillL b old i =@ a ⋆ K) (hi : i < old.length)
    (hw : old.length < 2 ^ 64) (a' : BitVec 64) (ha : a' = a + BitVec.ofNat 64 i) :
    (m.loadInt a' 1).isSome = true := by
  have hl := fillL_length b old i (by omega)
  have hoff : (a' - a).toNat = i := by
    rw [ha, show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega,
      BitVec.toNat_ofNat]; omega
  exact Val.loadInt_isSome_slice hm (Split.here _ _) (by rw [hoff, hl]; omega) (by rw [hl]; omega)

/-- The fill byte of `memset(dst, c, n)`. -/
abbrev fb8 (t : MachineData) : UInt8 := UInt8.ofBitVec ((arg1 t).setWidth 8)

variable [CodeEnv]

/-- The memset table, with the old bytes as a logical variable: the first `rcx` bytes filled. -/
abbrev msTable (need : Nat) (x : Parse.MsA × List UInt8) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "memset", s => s = t₀ ∧ x.2.length = (arg2 t₀).toNat
      ∧ (t₀.dmem =⋆ x.2 =@ arg0 t₀ ⋆ Rest need x.1.R ra t₀)
  | "memset.loop", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rax = arg0 t₀
      ∧ s.regs.get64 .rcx < arg2 t₀ ∧ x.2.length = (arg2 t₀).toNat
      ∧ (s.dmem =⋆ fillL (fb8 t₀) x.2 (s.regs.get64 .rcx).toNat =@ arg0 t₀ ⋆ Rest need x.1.R ra t₀)
  | "memset.done", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ s.regs.get64 .rax = arg0 t₀
      ∧ (s.dmem =⋆ List.replicate (arg2 t₀).toNat (fb8 t₀) =@ arg0 t₀ ⋆ Rest need x.1.R ra t₀)
  | _, _ => False

/-- The variant: bytes left at the loop. -/
abbrev msVar (_t : Unit) : Label → MachineData → Nat
  | "memset.loop", s => (s.regs.get64 .rdx - s.regs.get64 .rcx).toNat
  | "memset.done", _ => 0
  | _, _ => 2 ^ 64 + 1

theorem memset_pair (need : Nat) (hpl : Program.PlacedIn memsetT) :
    cenv.ProcSpec (entry "memset")
      (fun (x : Parse.MsA × List UInt8) ra t => x.2.length = (arg2 t).toNat
        ∧ (t.dmem =⋆ x.2 =@ arg0 t ⋆ Rest need x.1.R ra t))
      (fun x ra t s => Parse.MsPost need x.1 ra t s) := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := memsetT) (fun x ra t₀ => msTable need x ra t₀)
    (fun x ra t₀ s => s.regs.get64 .rax = arg0 t₀ ∧ Post' (fun _ _ => True)
      (fun t => List.replicate (arg2 t).toNat (fb8 t) =@ arg0 t) need x.1.R ra t₀ s)
    (msVar ()) (hblocks := ?_) (hpre := fun _ _ _ h => ⟨rfl, h⟩) (hpost := ?_)
  · intro x ra t₀
    have hf0 : fillL (fb8 t₀) x.2 0 = x.2 := by simp [fillL]
    have hr0 : x.2.length = 0 → List.replicate x.2.length (fb8 t₀) = x.2 := fun h => by
      rw [h, List.length_eq_zero_iff.mp h]; rfl
    cfg_cases [memsetT]
    · vcgen
      all_goals simp only [msTable.match_1.eq_1, Rest] at *
      all_goals call_simp
      all_goals grind_cells
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hsi, hdx, hax, hlt, hlen, hm⟩, hn⟩ := hs₀
      have hw : x.2.length < 2 ^ 64 := by rw [hlen]; exact (arg2 t₀).isLt
      have hc : (s₀.regs.get64 .rcx).toNat < x.2.length := by
        rw [hlen]; exact hlt
      have hc1 : (s₀.regs.get64 .rcx + 1#64).toNat = (s₀.regs.get64 .rcx).toNat + 1 := by
        have h := hlt
        rw [BitVec.lt_def] at h
        have := (arg2 t₀).isLt
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hst : ∀ a', a' = arg0 t₀ + s₀.regs.get64 .rcx → ∀ v : BitVec 8,
          UInt8.ofBitVec v = fb8 t₀ →
          s₀.dmem.storeInt a' 1 v.toInt =⋆ fillL (fb8 t₀) x.2 (s₀.regs.get64 .rcx + 1#64).toNat
            =@ arg0 t₀ ⋆ Rest need x.1.R ra t₀ := by
        intro a' ha v hv
        rw [hc1]
        exact fill_store hm hc hw a' (by rw [ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]) v hv
      have hld : ∀ a', a' = arg0 t₀ + s₀.regs.get64 .rcx → (s₀.dmem.loadInt a' 1).isSome = true :=
        fun a' ha => fill_load hm hc hw a' (by rw [ha, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      have hfull : (s₀.regs.get64 .rcx + 1#64).toNat = (arg2 t₀).toNat →
          fillL (fb8 t₀) x.2 (s₀.regs.get64 .rcx + 1#64).toNat
            = List.replicate (arg2 t₀).toNat (fb8 t₀) := fun h => by
        rw [h, ← hlen, fillL_full]
      have hv : (arg2 t₀ - (s₀.regs.get64 .rcx + 1#64)).toNat + 1
          = (arg2 t₀ - s₀.regs.get64 .rcx).toNat := by
        have h := hlt
        rw [BitVec.lt_def] at h
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hc1]; omega),
          BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hc1]
        omega
      simp only [msVar] at hn; rw [hdx] at hn
      clear hm
      vcgen
      all_goals subst_vars
      all_goals grind_cells
    · vcgen
      all_goals simp only [msTable.match_1.eq_3, Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · intro x ra t₀ s ⟨hr, h⟩
    exact ⟨hr, (post_of_ret h).1⟩

/-- The `memset` stand-in meets the value contract. -/
theorem memset_spec (need : Nat) (hpl : Program.PlacedIn memsetT) :
    Parse.MemsetValSpec need := by
  intro x ra t hpre
  have h : t.dmem =⋆ (arg2 t).toNat ?@ arg0 t ⋆ Rest need x.R ra t :=
    pre_of_call (F := fun t => (arg2 t).toNat ?@ arg0 t) hpre
  obtain ⟨-, bs, hl, hm⟩ := Block.sep_elim h
  exact memset_pair need hpl (x, bs) ra t ⟨hl, hm⟩

end Kraken.Examples.Sbr.WitEnv
