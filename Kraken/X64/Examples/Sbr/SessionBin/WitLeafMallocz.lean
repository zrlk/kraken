import Kraken.X64.Examples.Sbr.SessionBin.WitLeafMemset

/-!
# The witness stand-ins: the bump allocator `av_mallocz`

The stand-in `malloczT` meets `Init.AvMalloczSpec wX`: from a heap state of `wX` (next free
address `p`, free bytes `[p, wHeapEnd)`), a request of `n ≤ wHeapEnd - p` bytes returns `p`,
zeroed, and leaves the heap at `p + n` rounded up to 32 (the gap goes to the allocator's other
bytes); a larger request returns `NULL` and changes nothing.
-/

open Kraken.X64.Parser Kraken Kraken.SysV Std.WP Mem MachineWP
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.WitEnv

/-- The logical variables: the caller's memory, the heap pointer, the free bytes' old contents,
the allocator's other bytes. -/
structure MzA where
  R : Mem 64 → Prop
  p : BitVec 64
  old : List UInt8
  T : Mem 64 → Prop

/-- The heap state at pointer `q` with free bytes `free` and other bytes `T`. -/
def Heap (q : BitVec 64) (free : Mem 64 → Prop) (T : Mem 64 → Prop) : Mem 64 → Prop :=
  Apply.c8 wHeapPtr q ⋆ (free ⋆ T)

variable [CodeEnv]

/-- The table of `malloczT`. -/
abbrev mzTable (need : Nat) (x : MzA) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "av_mallocz", s => s = t₀ ∧ isAligned 32 x.p = true ∧ x.p.toNat ≤ wHeapEnd.toNat
      ∧ x.old.length = (wHeapEnd - x.p).toNat
      ∧ (t₀.dmem =⋆ Heap x.p (x.old =@ x.p) x.T ⋆ Rest need x.R ra t₀)
  | "av_mallocz.bump", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rax = x.p ∧ s.regs.get64 .r8 = wHeapPtr
      ∧ isAligned 32 x.p = true ∧ x.p.toNat ≤ wHeapEnd.toNat
      ∧ x.old.length = (wHeapEnd - x.p).toNat ∧ (arg0 t₀).toNat ≤ x.old.length
      ∧ (s.dmem =⋆ Heap x.p (x.old =@ x.p) x.T ⋆ Rest need x.R ra t₀)
  | "av_mallocz.loop", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rax = x.p
      ∧ s.regs.get64 .rcx < arg0 t₀
      ∧ x.old.length < 2 ^ 64 ∧ (arg0 t₀).toNat ≤ x.old.length
      ∧ (s.dmem =⋆ Heap (wNext x.p (arg0 t₀)) (fillL 0 x.old (s.regs.get64 .rcx).toNat =@ x.p) x.T
          ⋆ Rest need x.R ra t₀)
  | "av_mallocz.done", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ s.regs.get64 .rax = x.p ∧ (arg0 t₀).toNat ≤ x.old.length
      ∧ (s.dmem =⋆ Heap (wNext x.p (arg0 t₀)) (fillL 0 x.old (arg0 t₀).toNat =@ x.p) x.T
          ⋆ Rest need x.R ra t₀)
  | "av_mallocz.fail", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ x.old.length < (arg0 t₀).toNat
      ∧ (s.dmem =⋆ Heap x.p (x.old =@ x.p) x.T ⋆ Rest need x.R ra t₀)
  | _, _ => False
where
  /-- The next free address after `n` bytes at `p`: `p + n` rounded up to 32. -/
  wNext (p n : BitVec 64) : BitVec 64 := p + (n + 0x1f#64 &&& 0xffffffffffffffe0#64)

abbrev mzVar : Label → MachineData → Nat
  | "av_mallocz.bump", _ => 2 ^ 64 + 2
  | "av_mallocz.loop", s => (s.regs.get64 .rdi - s.regs.get64 .rcx).toNat + 1
  | "av_mallocz.done", _ => 0
  | "av_mallocz.fail", _ => 0
  | _, _ => 2 ^ 64 + 3

/-- What the two exits leave. -/
abbrev mzPost (need : Nat) (x : MzA) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ ((s.regs.get64 .rax = 0#64 ∧ x.old.length < (arg0 t₀).toNat ∧ (s.dmem =⋆ Heap x.p (x.old =@ x.p) x.T
        ⋆ (8 ?@ t₀.regs.get64 .rsp ⋆ (Reserve need (t₀.regs.get64 .rsp) ⋆ x.R))))
    ∨ (s.regs.get64 .rax = x.p ∧ (arg0 t₀).toNat ≤ x.old.length
      ∧ (s.dmem =⋆ Heap (mzTable.wNext x.p (arg0 t₀)) (fillL 0 x.old (arg0 t₀).toNat =@ x.p) x.T
        ⋆ (8 ?@ t₀.regs.get64 .rsp ⋆ (Reserve need (t₀.regs.get64 .rsp) ⋆ x.R)))))

theorem mallocz_pair (need : Nat) (hpl : Program.PlacedIn malloczT) :
    cenv.ProcSpec (entry "av_mallocz")
      (fun (x : MzA) ra t => isAligned 32 x.p = true ∧ x.p.toNat ≤ wHeapEnd.toNat
        ∧ x.old.length = (wHeapEnd - x.p).toNat
        ∧ (t.dmem =⋆ Heap x.p (x.old =@ x.p) x.T ⋆ Rest need x.R ra t))
      (mzPost need) := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := malloczT) (fun x ra t₀ => mzTable need x ra t₀)
    mzVar (hblocks := ?_) (hpre := fun _ _ _ h => ⟨rfl, h⟩)
  · intro x ra t₀
    have hf0 : fillL 0 x.old 0 = x.old := by simp [fillL]
    cfg_cases [malloczT]
    · vcgen
      all_goals simp only [mzTable.match_1.eq_1, Heap, Rest] at *
      all_goals call_simp
      all_goals grind_cells
    · refine Triple.pin fun s₀ hs₀ => ?_
      have hw0 : x.old.length < 2 ^ 64 := by
        obtain ⟨⟨-, -, -, -, -, -, -, -, hl, -⟩, -⟩ := hs₀; rw [hl]; exact BitVec.isLt _
      vcgen
      all_goals simp only [mzTable.match_1.eq_2, Heap, Rest, mzTable.wNext,
        show Int64.toBitVec 31 = 0x1f#64 from rfl,
        show BitVec.setWidth 64 (-32 : Int).toBitVec = 0xffffffffffffffe0#64 from rfl] at *
      all_goals call_simp
      all_goals grind_cells
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hax, hlt, hlen, hn0, hm⟩, hn⟩ := hs₀
      have hw : x.old.length < 2 ^ 64 := hlen
      have hc : (s₀.regs.get64 .rcx).toNat < x.old.length := by
        have h := hlt; rw [BitVec.lt_def] at h; omega
      have hc1 : (s₀.regs.get64 .rcx + 1#64).toNat = (s₀.regs.get64 .rcx).toNat + 1 := by
        have h := hlt
        rw [BitVec.lt_def] at h
        have := (arg0 t₀).isLt
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hrc : x.p + s₀.regs.get64 .rcx = x.p + BitVec.ofNat 64 (s₀.regs.get64 .rcx).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hm' : s₀.dmem =⋆ fillL 0 x.old (s₀.regs.get64 .rcx).toNat =@ x.p
          ⋆ (x.T ⋆ (Apply.c8 wHeapPtr (mzTable.wNext x.p (arg0 t₀)) ⋆ Rest need x.R ra t₀)) := by
        unfold Heap at hm
        rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l, Std.ExtHashMap.sep_assoc] at hm
        exact hm
      have hst : ∀ a', a' = x.p + s₀.regs.get64 .rcx → ∀ v : BitVec 8, UInt8.ofBitVec v = 0 →
          s₀.dmem.storeInt a' 1 v.toInt =⋆ Heap (mzTable.wNext x.p (arg0 t₀))
            (fillL 0 x.old (s₀.regs.get64 .rcx + 1#64).toNat =@ x.p) x.T ⋆ Rest need x.R ra t₀ := by
        intro a' ha v hv
        rw [hc1]
        have := fill_store hm' hc hw a' (by rw [ha, hrc]) v hv
        unfold Heap
        rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l, Std.ExtHashMap.sep_assoc]
        exact this
      have hld : ∀ a', a' = x.p + s₀.regs.get64 .rcx → (s₀.dmem.loadInt a' 1).isSome = true :=
        fun a' ha => fill_load hm' hc hw a' (by rw [ha, hrc])
      have hv : (arg0 t₀ - (s₀.regs.get64 .rcx + 1#64)).toNat + 1
          = (arg0 t₀ - s₀.regs.get64 .rcx).toNat := by
        have h := hlt
        rw [BitVec.lt_def] at h
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hc1]; omega),
          BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hc1]
        omega
      simp only [mzVar] at hn; rw [hdi] at hn
      have hfull : (s₀.regs.get64 .rcx + 1#64).toNat = (arg0 t₀).toNat →
          (s₀.regs.get64 .rcx + 1#64).toNat = (arg0 t₀).toNat := id
      clear hm hm' hf0 hc hrc hfull hw
      vcgen
      all_goals subst_vars
      all_goals grind_cells
    · vcgen
      all_goals simp only [mzTable.match_1.eq_4, Heap, Rest] at *
      all_goals call_simp
      all_goals grind_cells
    · vcgen
      all_goals simp only [mzTable.match_1.eq_5, Heap, Rest] at *
      all_goals call_simp
      all_goals grind_cells


/-! ## `AvMalloczSpec wX` -/


omit [CodeEnv] in
theorem nat_and_mask (n : Nat) (hn : n < 2 ^ 64) :
    n &&& (2 ^ 64 - 1 - 31) = n / 32 * 32 := by
  have e1 : (2 ^ 64 - 1 - 31 : Nat) = (2 ^ 59 - 1) <<< 5 := by decide
  have e2 : n / 32 * 32 = (n >>> 5) <<< 5 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [e1, e2]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h5 : 5 ≤ i
  · by_cases h64 : i < 64
    · have : i - 5 < 59 := by omega
      simp [h5, this, show 5 + (i - 5) = i by omega]
    · have : ¬ (i - 5 < 59) := by omega
      have hb : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [h5, this, show 5 + (i - 5) = i by omega, hb]
  · simp [h5]

omit [CodeEnv] in
/-- Masking with `-32` rounds down to a multiple of 32. -/
theorem and_mask_toNat (x : BitVec 64) :
    (x &&& 0xffffffffffffffe0#64).toNat = x.toNat / 32 * 32 := by
  have h : (0xffffffffffffffe0#64 : BitVec 64) = ~~~(31#64) := by decide
  rw [h, BitVec.toNat_and, BitVec.toNat_not]
  exact nat_and_mask _ x.isLt

omit [CodeEnv] in
theorem smono_l {P P' Q : Mem 64 → Prop} {m : Mem 64} (hp : ∀ m, P m → P' m)
    (h : (P ⋆ Q) m) : (P' ⋆ Q) m := by
  obtain ⟨u, v, h1, h2, hu, hv⟩ := h
  exact ⟨u, v, h1, h2, hp u hu, hv⟩

omit [CodeEnv] in
theorem smono_r {P Q Q' : Mem 64 → Prop} {m : Mem 64} (hq : ∀ m, Q m → Q' m)
    (h : (P ⋆ Q) m) : (P ⋆ Q') m := by
  obtain ⟨u, v, h1, h2, hu, hv⟩ := h
  exact ⟨u, v, h1, h2, hu, hq v hv⟩

omit [CodeEnv] in
/-- Packing a heap state at `q` into `wX`. -/
theorem wX_of {q : BitVec 64} {T K : Mem 64 → Prop} {m : Mem 64} (ha : isAligned 32 q = true)
    (hle : q.toNat ≤ wHeapEnd.toNat)
    (h : m =⋆ (Apply.c8 wHeapPtr q ⋆ ((wHeapEnd - q).toNat ?@ q ⋆ T)) ⋆ K) : m =⋆ wX ⋆ K :=
  smono_l (fun _ h' => ⟨q, ha, hle, smono_r (fun _ h'' => smono_r (fun _ _ => trivial) h'') h'⟩) h

omit [CodeEnv] in
/-- `wX` absorbs further bytes. -/
theorem wX_absorb {A K : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ (A ⋆ wX) ⋆ K) : m =⋆ wX ⋆ K := by
  refine smono_l (fun m' h' => ?_) h
  rw [Std.ExtHashMap.sep_comm] at h'
  obtain ⟨u, v, h1, h2, ⟨q, ha, hle, hq⟩, hA⟩ := h'
  refine ⟨q, ha, hle, ?_⟩
  have h3 : m' =⋆ (Apply.c8 wHeapPtr q ⋆ ((wHeapEnd - q).toNat ?@ q ⋆ fun _ => True)) ⋆ A :=
    ⟨u, v, h1, h2, hq, hA⟩
  have h4 : m' =⋆ Apply.c8 wHeapPtr q ⋆ ((wHeapEnd - q).toNat ?@ q ⋆ ((fun _ => True) ⋆ A)) :=
    Mem.ac h3
  exact smono_r (fun _ h'' => smono_r (fun _ _ => trivial) h'') h4

/-- The heap state at `p`, any further bytes: one state of `wX`. -/
def wXAt (p : BitVec 64) : Mem 64 → Prop :=
  Apply.c8 wHeapPtr p ⋆ ((wHeapEnd - p).toNat ?@ p ⋆ fun _ => True)

omit [CodeEnv] in
/-- The caller's memory at entry with heap state `p`, opened up: the free bytes' contents. -/
theorem pre_at {need : Nat} {R : Mem 64 → Prop} {ra : Int64} {t : MachineData} {p : BitVec 64}
    (h : t.dmem =⋆ wXAt p ⋆ (RetCell ra (t.regs.get64 .rsp)
      ⋆ (Reserve need (t.regs.get64 .rsp) ⋆ R))) :
    ∃ old, old.length = (wHeapEnd - p).toNat
      ∧ (t.dmem =⋆ Heap p (old =@ p) (fun _ => True) ⋆ Rest need R ra t) := by
  unfold wXAt at h
  have h4 : t.dmem =⋆ (wHeapEnd - p).toNat ?@ p ⋆ (Apply.c8 wHeapPtr p ⋆ ((fun _ => True)
      ⋆ (RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp) ⋆ R)))) :=
    Mem.ac h
  obtain ⟨-, old, hlen, h5⟩ := Block.sep_elim h4
  refine ⟨old, hlen, ?_⟩
  unfold Heap Rest
  rw [Val.eq]
  exact Mem.ac h5

omit [CodeEnv] in
/-- The caller's memory at entry, opened up: the heap pointer, the free bytes' contents. -/
theorem pre_wX {need : Nat} {R : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (h : CallPre need (wX ⋆ R) ra t) :
    ∃ p old, isAligned 32 p = true ∧ p.toNat ≤ wHeapEnd.toNat
      ∧ old.length = (wHeapEnd - p).toNat
      ∧ (t.dmem =⋆ Heap p (old =@ p) (fun _ => True) ⋆ Rest need R ra t) := by
  simp only [CallPre] at h
  have h' : t.dmem =⋆ wX ⋆ (RetCell ra (t.regs.get64 .rsp)
      ⋆ (Reserve need (t.regs.get64 .rsp) ⋆ R)) := Mem.ac h
  obtain ⟨u, v, h1, h2, ⟨p, ha, hle, hp⟩, hK⟩ := h'
  obtain ⟨old, hlen, hm⟩ := pre_at (p := p) ⟨u, v, h1, h2, hp, hK⟩
  exact ⟨p, old, ha, hle, hlen, hm⟩

omit [CodeEnv] in
/-- The heap left by a failed request is a state of `wX`. -/
theorem heap_wX0 {p : BitVec 64} {old : List UInt8} {T K : Mem 64 → Prop} {m : Mem 64}
    (ha : isAligned 32 p = true) (hle : p.toNat ≤ wHeapEnd.toNat)
    (hlen : old.length = (wHeapEnd - p).toNat)
    (h : m =⋆ Heap p (old =@ p) T ⋆ K) : m =⋆ wX ⋆ K := by
  unfold Heap at h
  rw [Val.eq] at h
  have h' : m =⋆ Eq (old.At p) ⋆ (Apply.c8 wHeapPtr p ⋆ (T ⋆ K)) := Mem.ac h
  have h'' := Block.sep_intro hlen (by have := (wHeapEnd - p).isLt; omega) h'
  exact wX_of (T := T) ha hle (Mem.ac h'')

omit [CodeEnv] in
/-- The heap left by a request of `a ≤ wHeapEnd - p` bytes: `a` zero bytes at `p`, and a state
of `wX` at `p + a` rounded up to 32. -/
theorem post_wX {p a : BitVec 64} {old : List UInt8} {K : Mem 64 → Prop} {m : Mem 64}
    (ha : isAligned 32 p = true) (hle : p.toNat ≤ wHeapEnd.toNat)
    (hlen : old.length = (wHeapEnd - p).toNat) (hn : a.toNat ≤ old.length)
    (h : m =⋆ Heap (mzTable.wNext p a) (fillL 0 old a.toNat =@ p) (fun _ => True) ⋆ K) :
    m =⋆ (Session.zs a.toNat =@ p ⋆ wX) ⋆ K := by
  have hp32 : p.toNat % 32 = 0 := by simpa [isAligned] using ha
  have hE : wHeapEnd.toNat = 0x400101000 := rfl
  have hsub : (wHeapEnd - p).toNat = wHeapEnd.toNat - p.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)
  have ha31 : (a + 0x1f#64).toNat = a.toNat + 31 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hr : (a + 0x1f#64 &&& 0xffffffffffffffe0#64).toNat = (a.toNat + 31) / 32 * 32 := by
    rw [and_mask_toNat, ha31]
  generalize hrd : (a + 0x1f#64 &&& 0xffffffffffffffe0#64) = r at hr
  have hq0 : mzTable.wNext p a = p + r := by rw [← hrd]; rfl
  rw [hq0] at h
  generalize hnd : a.toNat = n at hn hr h ⊢
  have hrle : r.toNat ≤ old.length := by omega
  have hnr : n ≤ r.toNat := by omega
  have hq : (p + r).toNat = p.toNat + r.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hqa : isAligned 32 (p + r) = true := by simp only [isAligned, hq]; simp; omega
  have hqle : (p + r).toNat ≤ wHeapEnd.toNat := by omega
  have hqsub : (wHeapEnd - (p + r)).toNat = old.length - r.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hqle)]; omega
  have hsplit : fillL 0 old n
      = Session.zs n ++ ((old.drop n).take (r.toNat - n) ++ old.drop r.toNat) := by
    have e : old.drop n = (old.drop n).take (r.toNat - n) ++ old.drop r.toNat := by
      conv => lhs; rw [← List.take_append_drop (r.toNat - n) (old.drop n)]
      rw [List.drop_drop, show n + (r.toNat - n) = r.toNat by omega]
    unfold fillL
    rw [← e]
  have hgl : ((old.drop n).take (r.toNat - n)).length = r.toNat - n := by
    simp only [List.length_take, List.length_drop]; omega
  have hrl : (old.drop r.toNat).length = old.length - r.toNat := by
    simp only [List.length_drop]
  have hw : old.length < 2 ^ 64 := by have := (wHeapEnd - p).isLt; omega
  unfold Heap at h
  rw [hsplit, Val.append_eq (Session.zs n) _ p (p + BitVec.ofNat 64 n) (by simp)
      (by simp only [List.length_replicate, List.length_append, hgl, hrl]; omega),
    Val.append_eq _ (old.drop r.toNat) (p + BitVec.ofNat 64 n) (p + r)
      (by
        rw [hgl]; apply BitVec.eq_of_toNat_eq
        rw [hq, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega)
      (by rw [hgl, hrl]; omega)] at h
  rw [Val.eq _ (old.drop r.toNat)] at h
  have h1 : m =⋆ Eq ((old.drop r.toNat).At (p + r)) ⋆ (Session.zs n =@ p
      ⋆ ((Apply.c8 wHeapPtr (p + r) ⋆ (((old.drop n).take (r.toNat - n) =@ (p + BitVec.ofNat 64 n))
      ⋆ fun _ => True)) ⋆ K)) := Mem.ac h
  have h2 := Block.sep_intro (hrl.trans hqsub.symm) (by omega) h1
  have h3 : m =⋆ Session.zs n =@ p ⋆ ((Apply.c8 wHeapPtr (p + r) ⋆ ((wHeapEnd - (p + r)).toNat ?@ (p + r)
      ⋆ (((old.drop n).take (r.toNat - n) =@ (p + BitVec.ofNat 64 n)) ⋆ fun _ => True))) ⋆ K) :=
    Mem.ac h2
  have h4 := smono_r (Q' := wX ⋆ K) (fun _ h' => wX_of hqa hqle h') h3
  exact Mem.ac h4

omit [CodeEnv] in
/-- What `mallocz_pair` leaves, read as `AvMalloczSpec`'s postcondition. -/
theorem mz_post {need : Nat} {R : Mem 64 → Prop} {ra : Int64} {t s : MachineData}
    {p : BitVec 64} {old : List UInt8}
    (ha : isAligned 32 p = true) (hle : p.toNat ≤ wHeapEnd.toNat)
    (hlen : old.length = (wHeapEnd - p).toNat)
    (h : mzPost need ⟨R, p, old, fun _ => True⟩ ra t s) :
    (s.regs.get64 .rax = 0#64 ∧ CallPost need (wX ⋆ R) ra t s)
      ∨ (s.regs.get64 .rax ≠ 0#64
        ∧ isAligned 32 (s.regs.get64 .rax) = true
        ∧ (s.regs.get64 .rax).toNat + (arg0 t).toNat ≤ 2 ^ 63
        ∧ CallPost need ((Session.zs (arg0 t).toNat =@ s.regs.get64 .rax ⋆ wX) ⋆ R) ra t s) := by
  obtain ⟨h1, h2, h3, ⟨hax, -, hm⟩ | ⟨hax, hn, hm⟩⟩ := h
  all_goals dsimp only at hm
  all_goals try dsimp only at hn
  all_goals try dsimp only at hax
  · exact Or.inl ⟨hax, h1, h2, h3, Mem.ac (heap_wX0 ha hle hlen hm)⟩
  · have hm' := post_wX ha hle hlen hn hm
    by_cases hp0 : p = 0#64
    · exact Or.inl ⟨hax.trans hp0, h1, h2, h3, Mem.ac (wX_absorb hm')⟩
    · right
      rw [hax]
      have hsub : (wHeapEnd - p).toNat = wHeapEnd.toNat - p.toNat :=
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)
      have hE : wHeapEnd.toNat = 0x400101000 := rfl
      exact ⟨hp0, ha, by omega, h1, h2, h3, Mem.ac hm'⟩

/-- **`av_mallocz`'s contract** holds of the stand-in, with init's state `wX`. -/
theorem mallocz_spec (need : Nat) (hpl : Program.PlacedIn malloczT) :
    Init.AvMalloczSpec wX need := by
  intro R ra t hpre
  obtain ⟨p, old, ha, hle, hlen, hm⟩ := pre_wX hpre
  exact eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, mz_post ha hle hlen hst.2⟩)
    (mallocz_pair need hpl ⟨R, p, old, fun _ => True⟩ ra t ⟨ha, hle, hlen, hm⟩)

/-- **`av_mallocz` succeeds** when the request fits: from heap state `p ≠ 0` (32-aligned, at
most `wHeapEnd`) and a request of at most `wHeapEnd - p` bytes, the stand-in returns `p`, holding
that many zero bytes, and leaves a state of `wX`. Before the first allocation (`p = wHeapStart`)
any request of at most `0x100000` bytes fits. -/
theorem mallocz_ok (need : Nat) (hpl : Program.PlacedIn malloczT) :
    cenv.ProcSpec (entry "av_mallocz")
      (fun (x : (Mem 64 → Prop) × BitVec 64) ra t => isAligned 32 x.2 = true
        ∧ x.2.toNat ≤ wHeapEnd.toNat ∧ x.2 ≠ 0#64 ∧ (arg0 t).toNat ≤ (wHeapEnd - x.2).toNat
        ∧ CallPre need (wXAt x.2 ⋆ x.1) ra t)
      (fun x ra t s => s.regs.get64 .rax = x.2
        ∧ CallPost need ((Session.zs (arg0 t).toNat =@ x.2 ⋆ wX) ⋆ x.1) ra t s) := by
  rintro ⟨R, p⟩ ra t ⟨ha, hle, -, hfit, hpre⟩
  dsimp only at ha hle hfit hpre ⊢
  simp only [CallPre] at hpre
  obtain ⟨old, hlen, hm⟩ := pre_at (p := p) (R := R) (need := need) (ra := ra) (Mem.ac hpre)
  refine eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, ?_⟩)
    (mallocz_pair need hpl ⟨R, p, old, fun _ => True⟩ ra t ⟨ha, hle, hlen, hm⟩)
  obtain ⟨h1, h2, h3, ⟨-, hlt, -⟩ | ⟨hax, hn, hm'⟩⟩ := hst.2
  · exact absurd hlt (by dsimp only; omega)
  · dsimp only at hax hn hm'
    exact ⟨hax, h1, h2, h3, Mem.ac (post_wX ha hle hlen hn hm')⟩

omit [CodeEnv] in
/-- The heap before the first allocation is the state `wHeapStart` of `wX`. -/
theorem wXAt_start {T : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ (Apply.c8 wHeapPtr wHeapStart ⋆ 0x100000 ?@ wHeapStart) ⋆ T) :
    m =⋆ wXAt wHeapStart ⋆ T := by
  have hb : m =⋆ ((Apply.c8 wHeapPtr wHeapStart ⋆ ((wHeapEnd - wHeapStart).toNat ?@ wHeapStart
      ⋆ Std.ExtHashMap.emp))) ⋆ T := by
    rw [Std.ExtHashMap.sep_emp]; exact h
  exact smono_l (fun _ h' => smono_r (fun _ h'' => smono_r (fun _ _ => trivial) h'') h') hb

end Kraken.Examples.Sbr.WitEnv
