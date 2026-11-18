import Kraken.X64.Examples.Sbr.SessionBin.WitLeafBasic
import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# The witness stand-ins: `memcpy`

The byte loop `memcpyT` meets `memcpy`'s value contract `Parse.MemcpyValSpec`: the old bytes of
`dst[n]` are a logical variable (`memcpy_pair`); the loop invariant is that the first `rcx` of
them are the source's (`copyL`).
-/

open Kraken.X64.Parser Kraken Kraken.SysV Std.WP Mem MachineWP
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.WitEnv

/-- The first `i` bytes of `old` replaced by those of `src`. -/
def copyL (src old : List UInt8) (i : Nat) : List UInt8 := src.take i ++ old.drop i

theorem copyL_length (src old : List UInt8) (i : Nat) (h : i ≤ old.length)
    (hs : src.length = old.length) : (copyL src old i).length = old.length := by
  simp only [copyL, List.length_append, List.length_take, List.length_drop]; omega

theorem copyL_succ (src old : List UInt8) (i : Nat) (h : i < old.length)
    (hs : src.length = old.length) :
    (copyL src old i).take i ++ [src.getD i 0] ++ (copyL src old i).drop (i + 1)
      = copyL src old (i + 1) := by
  have hl : (src.take i).length = i := by simp; omega
  have h1 : (copyL src old i).take i = src.take i := by
    simp [copyL, hl]
  have h2 : (copyL src old i).drop (i + 1) = old.drop (i + 1) := by
    simp only [copyL, List.drop_append, hl, List.drop_drop,
      show i + 1 - i = 1 by omega, List.drop_eq_nil_of_le (show (src.take i).length ≤ i + 1 by omega),
      List.nil_append]
  rw [h1, h2, copyL, List.take_add_one, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

theorem copyL_full (src old : List UInt8) (hs : src.length = old.length) :
    copyL src old old.length = src := by
  simp [copyL, ← hs]

theorem tb1 (v : BitVec 8) : Int.toBytes 1 v.toInt = [UInt8.ofBitVec v] := by
  revert v; decide

theorem ob1 (b : UInt8) : UInt8.ofBitVec (BitVec.ofInt 8 (Int.ofBytes [b])) = b := by
  cases b with | ofBitVec v => ?_
  revert v; decide

theorem drop_take1 (l : List UInt8) (j : Nat) (hj : j < l.length) :
    (l.drop j).take 1 = [l.getD j 0] := by
  induction j generalizing l with
  | zero => cases l <;> simp_all
  | succ j ih =>
    cases l with
    | nil => simp at hj
    | cons x l =>
      simp only [List.drop_succ_cons, List.getD_cons_succ]
      exact ih l (by simp at hj; omega)

theorem off_eq (a : BitVec 64) (i : Nat) (hi : i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i - a).toNat = i := by
  rw [show ∀ x y : BitVec 64, x + y - x = y from fun x y => by bv_omega, BitVec.toNat_ofNat]
  omega

/-- A byte store at offset `i` of a partly copied cell copies one more byte. -/
theorem copy_store {m : Mem 64} {src old : List UInt8} {i : Nat} {a : BitVec 64}
    {K : Mem 64 → Prop} (hm : m =⋆ copyL src old i =@ a ⋆ K) (hi : i < old.length)
    (hs : src.length = old.length) (hw : old.length < 2 ^ 64) (a' : BitVec 64)
    (ha : a' = a + BitVec.ofNat 64 i) (v : BitVec 8) (hv : UInt8.ofBitVec v = src.getD i 0) :
    m.storeInt a' 1 v.toInt =⋆ copyL src old (i + 1) =@ a ⋆ K := by
  have hl := copyL_length src old i (by omega) hs
  have hoff : (a' - a).toNat = i := by rw [ha]; exact off_eq a i (by omega)
  have := Val.storeInt_slice_split (n := 1) hm (Split.here _ _) (by rw [hoff, hl]; omega)
    (by rw [hl]; omega) v.toInt
  rw [hoff, tb1, hv, copyL_succ src old i hi hs] at this
  exact this

/-- A byte load at offset `i` of a partly copied cell is defined. -/
theorem copy_load {m : Mem 64} {src old : List UInt8} {i : Nat} {a : BitVec 64}
    {K : Mem 64 → Prop} (hm : m =⋆ copyL src old i =@ a ⋆ K) (hi : i < old.length)
    (hs : src.length = old.length) (hw : old.length < 2 ^ 64) (a' : BitVec 64)
    (ha : a' = a + BitVec.ofNat 64 i) : (m.loadInt a' 1).isSome = true := by
  have hl := copyL_length src old i (by omega) hs
  have hoff : (a' - a).toNat = i := by rw [ha]; exact off_eq a i (by omega)
  exact Val.loadInt_isSome_slice hm (Split.here _ _) (by rw [hoff, hl]; omega) (by rw [hl]; omega)

/-- A byte load at offset `i` of the source: byte `i`. -/
theorem src_load {m : Mem 64} {src : List UInt8} {i : Nat} {a : BitVec 64} {R K : Mem 64 → Prop}
    (hm : m =⋆ K) (hs : Split (src =@ a) R K) (hi : i < src.length) (hw : src.length < 2 ^ 64)
    (a' : BitVec 64) (ha : a' = a + BitVec.ofNat 64 i) :
    m.loadInt a' 1 = some (Int.ofBytes [src.getD i 0]) := by
  have hoff : (a' - a).toNat = i := by rw [ha]; exact off_eq a i (by omega)
  rw [Val.loadInt_slice_split hm hs (by rw [hoff]; omega) (by omega), hoff, drop_take1 src i hi]

variable [CodeEnv]

/-- The memcpy table, with the old bytes of `dst` as a logical variable: the first `rcx` bytes
copied. -/
abbrev mcTable (need : Nat) (x : Parse.McA × List UInt8) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "memcpy", s => s = t₀ ∧ x.1.src.length = (arg2 t₀).toNat ∧ x.2.length = (arg2 t₀).toNat
      ∧ (t₀.dmem =⋆ (x.1.src =@ arg1 t₀ ⋆ x.2 =@ arg0 t₀) ⋆ Rest need x.1.R ra t₀)
  | "memcpy.loop", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .rcx < arg2 t₀ ∧ x.1.src.length = (arg2 t₀).toNat
      ∧ x.2.length = (arg2 t₀).toNat
      ∧ (s.dmem =⋆ (x.1.src =@ arg1 t₀ ⋆ copyL x.1.src x.2 (s.regs.get64 .rcx).toNat =@ arg0 t₀)
          ⋆ Rest need x.1.R ra t₀)
  | "memcpy.done", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ (x.1.src =@ arg1 t₀ ⋆ x.1.src =@ arg0 t₀) ⋆ Rest need x.1.R ra t₀)
  | _, _ => False

/-- The variant: bytes left at the loop. -/
abbrev mcVar (_t : Unit) : Label → MachineData → Nat
  | "memcpy.loop", s => (s.regs.get64 .rdx - s.regs.get64 .rcx).toNat
  | "memcpy.done", _ => 0
  | _, _ => 2 ^ 64 + 1

theorem memcpy_pair (need : Nat) (hpl : Program.PlacedIn memcpyT) :
    cenv.ProcSpec (entry "memcpy")
      (fun (x : Parse.McA × List UInt8) ra t => x.1.src.length = (arg2 t).toNat
        ∧ x.2.length = (arg2 t).toNat
        ∧ (t.dmem =⋆ (x.1.src =@ arg1 t ⋆ x.2 =@ arg0 t) ⋆ Rest need x.1.R ra t))
      (fun x ra t s => Parse.McPost need x.1 ra t s) := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := memcpyT) (fun x ra t₀ => mcTable need x ra t₀)
    (fun x ra t₀ s => Post' (fun _ _ => True)
      (fun t => x.1.src =@ arg1 t ⋆ x.1.src =@ arg0 t) need x.1.R ra t₀ s)
    (mcVar ()) (hblocks := ?_) (hpre := fun _ _ _ h => ⟨rfl, h⟩) (hpost := ?_)
  · intro x ra t₀
    have hf0 : copyL x.1.src x.2 0 = x.2 := by simp [copyL]
    have hr0 : x.2.length = 0 → x.1.src.length = 0 → x.1.src = x.2 := fun h h' => by
      rw [List.length_eq_zero_iff.mp h, List.length_eq_zero_iff.mp h']
    cfg_cases [memcpyT]
    · vcgen
      all_goals simp only [mcTable.match_1.eq_1, Rest] at *
      all_goals call_simp
      all_goals grind_cells
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hsi, hdx, hlt, hls, hlen, hm⟩, hn⟩ := hs₀
      have hw : x.2.length < 2 ^ 64 := by rw [hlen]; exact (arg2 t₀).isLt
      have hc : (s₀.regs.get64 .rcx).toNat < x.2.length := by
        rw [hlen]; exact hlt
      have hss : x.1.src.length = x.2.length := by rw [hls, hlen]
      have hc1 : (s₀.regs.get64 .rcx + 1#64).toNat = (s₀.regs.get64 .rcx).toNat + 1 := by
        have h := hlt
        rw [BitVec.lt_def] at h
        have := (arg2 t₀).isLt
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hrc : arg0 t₀ + s₀.regs.get64 .rcx
          = arg0 t₀ + BitVec.ofNat 64 (s₀.regs.get64 .rcx).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hrs : arg1 t₀ + s₀.regs.get64 .rcx
          = arg1 t₀ + BitVec.ofNat 64 (s₀.regs.get64 .rcx).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hm' : s₀.dmem =⋆ copyL x.1.src x.2 (s₀.regs.get64 .rcx).toNat =@ arg0 t₀
          ⋆ (x.1.src =@ arg1 t₀ ⋆ Rest need x.1.R ra t₀) := by
        rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at hm; exact hm
      have hsrc : ∀ a', a' = arg1 t₀ + s₀.regs.get64 .rcx →
          s₀.dmem.loadInt a' 1 = some (Int.ofBytes [x.1.src.getD (s₀.regs.get64 .rcx).toNat 0]) :=
        fun a' ha => src_load hm (Split.left (Split.here _ _) _) (by omega) (by omega) a'
          (by rw [ha, hrs])
      have hst : ∀ a', a' = arg0 t₀ + s₀.regs.get64 .rcx → ∀ v : BitVec 8,
          UInt8.ofBitVec v = x.1.src.getD (s₀.regs.get64 .rcx).toNat 0 →
          s₀.dmem.storeInt a' 1 v.toInt =⋆ (x.1.src =@ arg1 t₀
            ⋆ copyL x.1.src x.2 (s₀.regs.get64 .rcx + 1#64).toNat =@ arg0 t₀)
            ⋆ Rest need x.1.R ra t₀ := by
        intro a' ha v hv
        rw [hc1]
        have := copy_store hm' hc hss hw a' (by rw [ha, hrc]) v hv
        rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l (x.1.src =@ arg1 t₀)]
        exact this
      have hld : ∀ a', a' = arg0 t₀ + s₀.regs.get64 .rcx → (s₀.dmem.loadInt a' 1).isSome = true :=
        fun a' ha => copy_load hm' hc hss hw a' (by rw [ha, hrc])
      have hbyte : ∀ b : UInt8, UInt8.ofBitVec (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b]))))) = b := by
        intro b
        rw [show ∀ y : BitVec 8, BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 y)) = y
          from fun y => by apply BitVec.eq_of_toNat_eq; simp, ob1]
      have hfull : (s₀.regs.get64 .rcx + 1#64).toNat = (arg2 t₀).toNat →
          copyL x.1.src x.2 (s₀.regs.get64 .rcx + 1#64).toNat = x.1.src := fun h => by
        rw [h, ← hlen, copyL_full _ _ hss]
      have hv : (arg2 t₀ - (s₀.regs.get64 .rcx + 1#64)).toNat + 1
          = (arg2 t₀ - s₀.regs.get64 .rcx).toNat := by
        have h := hlt
        rw [BitVec.lt_def] at h
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hc1]; omega),
          BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hc1]
        omega
      simp only [mcVar] at hn; rw [hdx] at hn
      clear hm hm'
      vcgen
      all_goals subst_vars
      all_goals grind_cells
    · vcgen
      all_goals simp only [mcTable.match_1.eq_3, Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · intro x ra t₀ s h
    exact (post_of_ret h).1

/-- The `memcpy` stand-in meets the value contract. -/
theorem memcpy_spec (need : Nat) (hpl : Program.PlacedIn memcpyT) :
    Parse.MemcpyValSpec need := by
  intro x ra t ⟨hpre, hl⟩
  have h : t.dmem =⋆ (x.src =@ arg1 t ⋆ (arg2 t).toNat ?@ arg0 t) ⋆ Rest need x.R ra t :=
    pre_of_call (F := fun t => x.src =@ arg1 t ⋆ (arg2 t).toNat ?@ arg0 t) hpre
  rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at h
  obtain ⟨-, bs, hb, hm⟩ := Block.sep_elim h
  refine memcpy_pair need hpl (x, bs) ra t ⟨hl, hb, ?_⟩
  rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l]
  exact hm

end Kraken.Examples.Sbr.WitEnv
