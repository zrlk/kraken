import Kraken.X64.Examples.Sbr.SessionBin.WitLeafMemcpy

/-!
# The witness stand-ins: `ff_sbrdsp_init`

The straight-line text `sbrdspT` (fourteen `lea`/`mov` pairs, two per block) meets
`Init.SbrDspInitSpec`: it leaves the slots `wSlots` (the routines of `DspSlotsOK`). The block
invariant: the first `j` slots stored (`(slotL.take j).map fb`, flattened) in front of the rest
of the old bytes.
-/

open Kraken.X64.Parser Kraken Kraken.SysV Std.WP Mem MachineWP
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.WitEnv

/-- The first `j` 8-byte values of `L` in front of the old bytes from `8 j` on. -/
def chunkL (L : List Int64) (old : List UInt8) (j : Nat) : List UInt8 :=
  ((L.take j).map Init.fb).flatten ++ old.drop (8 * j)

theorem flat_len : ∀ L : List Int64, ((L.map Init.fb).flatten).length = 8 * L.length
  | [] => rfl
  | f :: L => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, Init.fb,
      Int.toBytes_length, flat_len L, List.length_cons]
    omega

theorem chunkL_length (L : List Int64) (old : List UInt8) (j : Nat) (hj : j ≤ L.length)
    (ho : old.length = 8 * L.length) : (chunkL L old j).length = old.length := by
  simp only [chunkL, List.length_append, flat_len, List.length_take, List.length_drop]
  omega

theorem flat_take_succ (L : List Int64) (j : Nat) (hj : j < L.length) :
    ((L.take (j + 1)).map Init.fb).flatten = ((L.take j).map Init.fb).flatten ++ Init.fb L[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem chunkL_succ (L : List Int64) (old : List UInt8) (j : Nat) (hj : j < L.length)
    (_ho : old.length = 8 * L.length) :
    (chunkL L old j).take (8 * j) ++ Init.fb L[j] ++ (chunkL L old j).drop (8 * j + 8)
      = chunkL L old (j + 1) := by
  have hl : (((L.take j).map Init.fb).flatten).length = 8 * j := by
    rw [flat_len, List.length_take]; omega
  have h1 : (chunkL L old j).take (8 * j) = ((L.take j).map Init.fb).flatten := by
    rw [chunkL, List.take_append, hl, Nat.sub_self, List.take_zero, List.append_nil,
      List.take_of_length_le (Nat.le_of_eq hl)]
  have h2 : (chunkL L old j).drop (8 * j + 8) = old.drop (8 * (j + 1)) := by
    rw [chunkL, List.drop_append, hl, List.drop_drop,
      List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append]
    congr 1; omega
  rw [h1, h2, chunkL, flat_take_succ L j hj, List.append_assoc]

theorem chunkL_full (L : List Int64) (old : List UInt8) (ho : old.length = 8 * L.length) :
    chunkL L old L.length = (L.map Init.fb).flatten := by
  simp [chunkL, ho]

theorem chunkL_zero (L : List Int64) (old : List UInt8) : chunkL L old 0 = old := by
  simp [chunkL]

/-- An 8-byte store of slot `j` at offset `8 j`. -/
theorem chunk_store {m : Mem 64} {L : List Int64} {old : List UInt8} {j : Nat} {a : BitVec 64}
    {K : Mem 64 → Prop} (hm : m =⋆ chunkL L old j =@ a ⋆ K) (hj : j < L.length)
    (ho : old.length = 8 * L.length) (hw : old.length < 2 ^ 63) (a' : BitVec 64)
    (ha : a' = a + BitVec.ofNat 64 (8 * j)) (v : BitVec 64) (hv : v = L[j].toBitVec) :
    m.storeInt a' 8 v.toInt =⋆ chunkL L old (j + 1) =@ a ⋆ K := by
  have hl := chunkL_length L old j (by omega) ho
  have hoff : (a' - a).toNat = 8 * j := by rw [ha]; exact off_eq a _ (by omega)
  have := Val.storeInt_slice_split (n := 8) hm (Split.here _ _) (by rw [hoff, hl]; omega)
    (by rw [hl]; omega) v.toInt
  subst hv
  rw [hoff] at this
  rw [← chunkL_succ L old j hj ho]
  exact this

/-- An 8-byte store at offset `8 j` is defined. -/
theorem chunk_load {m : Mem 64} {L : List Int64} {old : List UInt8} {j : Nat} {a : BitVec 64}
    {K : Mem 64 → Prop} (hm : m =⋆ chunkL L old j =@ a ⋆ K) (hj : j < L.length)
    (ho : old.length = 8 * L.length) (hw : old.length < 2 ^ 63) (a' : BitVec 64)
    (ha : a' = a + BitVec.ofNat 64 (8 * j)) : (m.loadInt a' 8).isSome = true := by
  have hl := chunkL_length L old j (by omega) ho
  have hoff : (a' - a).toNat = 8 * j := by rw [ha]; exact off_eq a _ (by omega)
  exact Val.loadInt_isSome_slice hm (Split.here _ _) (by rw [hoff, hl]; omega) (by rw [hl]; omega)

variable [CodeEnv]

/-- The slots `ff_sbrdsp_init_x86` leaves, as the stand-in stores them. -/
def wSlots : Init.Slots :=
  ⟨entry "ff_sbr_sum64x5_sse", entry "ff_sbr_sum_square_sse", entry "ff_sbr_neg_odd_64_sse",
    entry "ff_sbr_qmf_pre_shuffle_sse2", entry "ff_sbr_qmf_post_shuffle_sse",
    entry "ff_sbr_qmf_deint_neg_sse", entry "ff_sbr_qmf_deint_bfly_sse2",
    entry "ff_sbr_autocorrelate_sse", entry "ff_sbr_hf_gen_sse", entry "ff_sbr_hf_g_filt_sse",
    entry "ff_sbr_hf_apply_noise_0_sse2", entry "ff_sbr_hf_apply_noise_1_sse2",
    entry "ff_sbr_hf_apply_noise_2_sse2", entry "ff_sbr_hf_apply_noise_3_sse2"⟩

theorem wSlots_ok : Init.DspSlotsOK wSlots :=
  ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The slots in `sbr->dsp` order. -/
def slotL : List Int64 :=
  [wSlots.sum64x5, wSlots.sumSquare, wSlots.negOdd64, wSlots.preShuffle, wSlots.postShuffle,
    wSlots.deintNeg, wSlots.deintBfly, wSlots.autocorr, wSlots.hfGen, wSlots.gfilt,
    wSlots.noise0, wSlots.noise1, wSlots.noise2, wSlots.noise3]

theorem slotL_length : slotL.length = 14 := rfl

theorem slotL_bytes : (slotL.map Init.fb).flatten = wSlots.bytes := by
  simp [slotL, Init.Slots.bytes, List.append_assoc]

/-- The memory after `j` slots (a `def`, so that `grind` moves it whole). -/
def DM (X : Mem 64 → Prop) (need : Nat) (x : (Mem 64 → Prop) × List UInt8) (ra : Int64)
    (t₀ : MachineData) (j : Nat) : Mem 64 → Prop :=
  (chunkL slotL x.2 j =@ arg0 t₀ ⋆ X) ⋆ Rest need x.1 ra t₀

/-- The table of `sbrdspT`: at block `2 i`, the first `2 i` slots stored. -/
abbrev dspTable (X : Mem 64 → Prop) (need : Nat) (x : (Mem 64 → Prop) × List UInt8) (ra : Int64)
    (t₀ : MachineData) : Label → MachineData → Prop
  | "ff_sbrdsp_init", s => s = t₀ ∧ x.2.length = 0x70
      ∧ (t₀.dmem =⋆ (x.2 =@ arg0 t₀ ⋆ X) ⋆ Rest need x.1 ra t₀)
  | "ff_sbrdsp_init.s2", s => DspAt X need x ra t₀ s 2
  | "ff_sbrdsp_init.s4", s => DspAt X need x ra t₀ s 4
  | "ff_sbrdsp_init.s6", s => DspAt X need x ra t₀ s 6
  | "ff_sbrdsp_init.s8", s => DspAt X need x ra t₀ s 8
  | "ff_sbrdsp_init.s10", s => DspAt X need x ra t₀ s 10
  | "ff_sbrdsp_init.s12", s => DspAt X need x ra t₀ s 12
  | "ff_sbrdsp_init.done", s => DspAt X need x ra t₀ s 14
  | _, _ => False
where
  /-- After `j` slots. -/
  DspAt (X : Mem 64 → Prop) (need : Nat) (x : (Mem 64 → Prop) × List UInt8) (ra : Int64)
      (t₀ s : MachineData) (j : Nat) : Prop :=
    s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
    ∧ SavedRegs t₀ s ∧ s.regs.get64 .rdi = arg0 t₀ ∧ x.2.length = 0x70
    ∧ DM X need x ra t₀ j s.dmem

/-- The variant: blocks left. -/
abbrev dspVar : Label → MachineData → Nat
  | "ff_sbrdsp_init.s2", _ => 6
  | "ff_sbrdsp_init.s4", _ => 5
  | "ff_sbrdsp_init.s6", _ => 4
  | "ff_sbrdsp_init.s8", _ => 3
  | "ff_sbrdsp_init.s10", _ => 2
  | "ff_sbrdsp_init.s12", _ => 1
  | "ff_sbrdsp_init.done", _ => 0
  | _, _ => 8

/-- A slot store, in the table's memory shape. -/
theorem dsp_store {m : Mem 64} {old : List UInt8} {j : Nat} {a : BitVec 64} {X R : Mem 64 → Prop}
    (hm : m =⋆ (chunkL slotL old j =@ a ⋆ X) ⋆ R) (hj : j < 14) (hl : old.length = 0x70)
    (a' : BitVec 64) (ha : a' = a + BitVec.ofNat 64 (8 * j)) (v : BitVec 64)
    (hv : v = (slotL.getD j 0).toBitVec) :
    m.storeInt a' 8 v.toInt =⋆ (chunkL slotL old (j + 1) =@ a ⋆ X) ⋆ R := by
  have hj' : j < slotL.length := by rw [slotL_length]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some] at hv
  rw [Std.ExtHashMap.sep_assoc] at hm ⊢
  exact chunk_store hm (by rw [slotL_length]; exact hj) (by rw [hl, slotL_length])
    (by rw [hl]; decide) a' ha v hv

/-- A slot load is defined, in the table's memory shape. -/
theorem dsp_load {m : Mem 64} {old : List UInt8} {j : Nat} {a : BitVec 64} {X R : Mem 64 → Prop}
    (hm : m =⋆ (chunkL slotL old j =@ a ⋆ X) ⋆ R) (hj : j < 14) (hl : old.length = 0x70)
    (a' : BitVec 64) (ha : a' = a + BitVec.ofNat 64 (8 * j)) : (m.loadInt a' 8).isSome = true := by
  rw [Std.ExtHashMap.sep_assoc] at hm
  exact chunk_load hm (by rw [slotL_length]; exact hj) (by rw [hl, slotL_length])
    (by rw [hl]; decide) a' ha

theorem sbrdsp_pair (X : Mem 64 → Prop) (need : Nat) (hpl : Program.PlacedIn sbrdspT) :
    cenv.ProcSpec (entry "ff_sbrdsp_init")
      (fun (x : (Mem 64 → Prop) × List UInt8) ra t => x.2.length = 0x70
        ∧ (t.dmem =⋆ (x.2 =@ arg0 t ⋆ X) ⋆ Rest need x.1 ra t))
      (fun x ra t s => CallPost need ((wSlots.bytes =@ arg0 t ⋆ X) ⋆ x.1) ra t s) := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := sbrdspT) (dspTable X need)
    (fun x ra t₀ s => Post' (fun _ _ => True) (fun t => wSlots.bytes =@ arg0 t ⋆ X) need x.1
      ra t₀ s)
    dspVar (hblocks := ?_) (hpre := fun _ _ _ h => ⟨rfl, h⟩) (hpost := ?_)
  · intro x ra t₀
    cfg_cases [sbrdspT]
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hs, hl, hm⟩, hn⟩ := hs₀
      rw [← chunkL_zero slotL x.2] at hm
      change DM X need x ra t₀ 0 t₀.dmem at hm
      have l0 : ∀ (m : Mem 64), DM X need x ra t₀ 0 m →
          ∀ a', a' = arg0 t₀ + 0 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h0 : ∀ (m : Mem 64), DM X need x ra t₀ 0 m →
          ∀ a', a' = arg0 t₀ + 0 → ∀ v : BitVec 64, v = (entry "ff_sbr_sum64x5_sse").toBitVec →
          DM X need x ra t₀ 1 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have l1 : ∀ (m : Mem 64), DM X need x ra t₀ 1 m →
          ∀ a', a' = arg0 t₀ + 8 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h1 : ∀ (m : Mem 64), DM X need x ra t₀ 1 m →
          ∀ a', a' = arg0 t₀ + 8 → ∀ v : BitVec 64, v = (entry "ff_sbr_sum_square_sse").toBitVec →
          DM X need x ra t₀ 2 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have m1 := h0 s₀.dmem (by rw [hs]; exact hm) (s₀.regs.get64 .rdi + 0) (by rw [hs]) _ rfl
      have m2 := h1 _ m1 (s₀.regs.get64 .rdi + 8) (by rw [hs]) _ rfl
      have q1 := l0 s₀.dmem (by rw [hs]; exact hm) (s₀.regs.get64 .rdi + 0) (by rw [hs])
      have q2 := l1 _ m1 (s₀.regs.get64 .rdi + 8) (by rw [hs])
      clear h0 h1 l0 l1 hm m1
      vcgen
      all_goals (try simp only [dspTable.DspAt] at *)
      all_goals grind
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hl, hm⟩, hn⟩ := hs₀
      have l0 : ∀ (m : Mem 64), DM X need x ra t₀ 2 m →
          ∀ a', a' = arg0 t₀ + 16 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h0 : ∀ (m : Mem 64), DM X need x ra t₀ 2 m →
          ∀ a', a' = arg0 t₀ + 16 → ∀ v : BitVec 64, v = (entry "ff_sbr_neg_odd_64_sse").toBitVec →
          DM X need x ra t₀ 3 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have l1 : ∀ (m : Mem 64), DM X need x ra t₀ 3 m →
          ∀ a', a' = arg0 t₀ + 24 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h1 : ∀ (m : Mem 64), DM X need x ra t₀ 3 m →
          ∀ a', a' = arg0 t₀ + 24 → ∀ v : BitVec 64, v = (entry "ff_sbr_qmf_pre_shuffle_sse2").toBitVec →
          DM X need x ra t₀ 4 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have m1 := h0 s₀.dmem hm (s₀.regs.get64 .rdi + 16) (by rw [hdi]) _ rfl
      have m2 := h1 _ m1 (s₀.regs.get64 .rdi + 24) (by rw [hdi]) _ rfl
      have q1 := l0 s₀.dmem hm (s₀.regs.get64 .rdi + 16) (by rw [hdi])
      have q2 := l1 _ m1 (s₀.regs.get64 .rdi + 24) (by rw [hdi])
      clear h0 h1 l0 l1 hm m1
      vcgen
      all_goals (try simp only [dspTable.DspAt] at *)
      all_goals grind
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hl, hm⟩, hn⟩ := hs₀
      have l0 : ∀ (m : Mem 64), DM X need x ra t₀ 4 m →
          ∀ a', a' = arg0 t₀ + 32 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h0 : ∀ (m : Mem 64), DM X need x ra t₀ 4 m →
          ∀ a', a' = arg0 t₀ + 32 → ∀ v : BitVec 64, v = (entry "ff_sbr_qmf_post_shuffle_sse").toBitVec →
          DM X need x ra t₀ 5 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have l1 : ∀ (m : Mem 64), DM X need x ra t₀ 5 m →
          ∀ a', a' = arg0 t₀ + 40 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h1 : ∀ (m : Mem 64), DM X need x ra t₀ 5 m →
          ∀ a', a' = arg0 t₀ + 40 → ∀ v : BitVec 64, v = (entry "ff_sbr_qmf_deint_neg_sse").toBitVec →
          DM X need x ra t₀ 6 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have m1 := h0 s₀.dmem hm (s₀.regs.get64 .rdi + 32) (by rw [hdi]) _ rfl
      have m2 := h1 _ m1 (s₀.regs.get64 .rdi + 40) (by rw [hdi]) _ rfl
      have q1 := l0 s₀.dmem hm (s₀.regs.get64 .rdi + 32) (by rw [hdi])
      have q2 := l1 _ m1 (s₀.regs.get64 .rdi + 40) (by rw [hdi])
      clear h0 h1 l0 l1 hm m1
      vcgen
      all_goals (try simp only [dspTable.DspAt] at *)
      all_goals grind
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hl, hm⟩, hn⟩ := hs₀
      have l0 : ∀ (m : Mem 64), DM X need x ra t₀ 6 m →
          ∀ a', a' = arg0 t₀ + 48 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h0 : ∀ (m : Mem 64), DM X need x ra t₀ 6 m →
          ∀ a', a' = arg0 t₀ + 48 → ∀ v : BitVec 64, v = (entry "ff_sbr_qmf_deint_bfly_sse2").toBitVec →
          DM X need x ra t₀ 7 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have l1 : ∀ (m : Mem 64), DM X need x ra t₀ 7 m →
          ∀ a', a' = arg0 t₀ + 56 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h1 : ∀ (m : Mem 64), DM X need x ra t₀ 7 m →
          ∀ a', a' = arg0 t₀ + 56 → ∀ v : BitVec 64, v = (entry "ff_sbr_autocorrelate_sse").toBitVec →
          DM X need x ra t₀ 8 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have m1 := h0 s₀.dmem hm (s₀.regs.get64 .rdi + 48) (by rw [hdi]) _ rfl
      have m2 := h1 _ m1 (s₀.regs.get64 .rdi + 56) (by rw [hdi]) _ rfl
      have q1 := l0 s₀.dmem hm (s₀.regs.get64 .rdi + 48) (by rw [hdi])
      have q2 := l1 _ m1 (s₀.regs.get64 .rdi + 56) (by rw [hdi])
      clear h0 h1 l0 l1 hm m1
      vcgen
      all_goals (try simp only [dspTable.DspAt] at *)
      all_goals grind
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hl, hm⟩, hn⟩ := hs₀
      have l0 : ∀ (m : Mem 64), DM X need x ra t₀ 8 m →
          ∀ a', a' = arg0 t₀ + 64 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h0 : ∀ (m : Mem 64), DM X need x ra t₀ 8 m →
          ∀ a', a' = arg0 t₀ + 64 → ∀ v : BitVec 64, v = (entry "ff_sbr_hf_gen_sse").toBitVec →
          DM X need x ra t₀ 9 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have l1 : ∀ (m : Mem 64), DM X need x ra t₀ 9 m →
          ∀ a', a' = arg0 t₀ + 72 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h1 : ∀ (m : Mem 64), DM X need x ra t₀ 9 m →
          ∀ a', a' = arg0 t₀ + 72 → ∀ v : BitVec 64, v = (entry "ff_sbr_hf_g_filt_sse").toBitVec →
          DM X need x ra t₀ 10 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have m1 := h0 s₀.dmem hm (s₀.regs.get64 .rdi + 64) (by rw [hdi]) _ rfl
      have m2 := h1 _ m1 (s₀.regs.get64 .rdi + 72) (by rw [hdi]) _ rfl
      have q1 := l0 s₀.dmem hm (s₀.regs.get64 .rdi + 64) (by rw [hdi])
      have q2 := l1 _ m1 (s₀.regs.get64 .rdi + 72) (by rw [hdi])
      clear h0 h1 l0 l1 hm m1
      vcgen
      all_goals (try simp only [dspTable.DspAt] at *)
      all_goals grind
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hl, hm⟩, hn⟩ := hs₀
      have l0 : ∀ (m : Mem 64), DM X need x ra t₀ 10 m →
          ∀ a', a' = arg0 t₀ + 80 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h0 : ∀ (m : Mem 64), DM X need x ra t₀ 10 m →
          ∀ a', a' = arg0 t₀ + 80 → ∀ v : BitVec 64, v = (entry "ff_sbr_hf_apply_noise_0_sse2").toBitVec →
          DM X need x ra t₀ 11 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have l1 : ∀ (m : Mem 64), DM X need x ra t₀ 11 m →
          ∀ a', a' = arg0 t₀ + 88 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h1 : ∀ (m : Mem 64), DM X need x ra t₀ 11 m →
          ∀ a', a' = arg0 t₀ + 88 → ∀ v : BitVec 64, v = (entry "ff_sbr_hf_apply_noise_1_sse2").toBitVec →
          DM X need x ra t₀ 12 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have m1 := h0 s₀.dmem hm (s₀.regs.get64 .rdi + 80) (by rw [hdi]) _ rfl
      have m2 := h1 _ m1 (s₀.regs.get64 .rdi + 88) (by rw [hdi]) _ rfl
      have q1 := l0 s₀.dmem hm (s₀.regs.get64 .rdi + 80) (by rw [hdi])
      have q2 := l1 _ m1 (s₀.regs.get64 .rdi + 88) (by rw [hdi])
      clear h0 h1 l0 l1 hm m1
      vcgen
      all_goals (try simp only [dspTable.DspAt] at *)
      all_goals grind
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hl, hm⟩, hn⟩ := hs₀
      have l0 : ∀ (m : Mem 64), DM X need x ra t₀ 12 m →
          ∀ a', a' = arg0 t₀ + 96 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h0 : ∀ (m : Mem 64), DM X need x ra t₀ 12 m →
          ∀ a', a' = arg0 t₀ + 96 → ∀ v : BitVec 64, v = (entry "ff_sbr_hf_apply_noise_2_sse2").toBitVec →
          DM X need x ra t₀ 13 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have l1 : ∀ (m : Mem 64), DM X need x ra t₀ 13 m →
          ∀ a', a' = arg0 t₀ + 104 → (m.loadInt a' 8).isSome = true :=
        fun m hm a' ha => dsp_load hm (by decide) hl a' (by subst ha; rfl)
      have h1 : ∀ (m : Mem 64), DM X need x ra t₀ 13 m →
          ∀ a', a' = arg0 t₀ + 104 → ∀ v : BitVec 64, v = (entry "ff_sbr_hf_apply_noise_3_sse2").toBitVec →
          DM X need x ra t₀ 14 (m.storeInt a' 8 v.toInt) :=
        fun m hm a' ha v hv => dsp_store hm (by decide) hl a' (by subst ha; rfl) v (by subst hv; rfl)
      have m1 := h0 s₀.dmem hm (s₀.regs.get64 .rdi + 96) (by rw [hdi]) _ rfl
      have m2 := h1 _ m1 (s₀.regs.get64 .rdi + 104) (by rw [hdi]) _ rfl
      have q1 := l0 s₀.dmem hm (s₀.regs.get64 .rdi + 96) (by rw [hdi])
      have q2 := l1 _ m1 (s₀.regs.get64 .rdi + 104) (by rw [hdi])
      clear h0 h1 l0 l1 hm m1
      vcgen
      all_goals (try simp only [dspTable.DspAt] at *)
      all_goals grind
    · refine Triple.pin fun s₀ hs₀ => ?_
      obtain ⟨⟨hsp, hbp, hsv, hdi, hl, hm⟩, hn⟩ := hs₀
      have hm' : s₀.dmem =⋆ (wSlots.bytes =@ arg0 t₀ ⋆ X) ⋆ Rest need x.1 ra t₀ := by
        have e : chunkL slotL x.2 14 = wSlots.bytes := by
          rw [← slotL_bytes, ← slotL_length, chunkL_full _ _ (by rw [hl]; rfl)]
        unfold DM at hm; rw [e] at hm; exact hm
      clear hm
      vcgen
      all_goals simp only [Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · intro x ra t₀ s h
    exact (post_of_ret h).1

/-- The `ff_sbrdsp_init` stand-in meets its contract. -/
theorem sbrdsp_spec (X : Mem 64 → Prop) (need : Nat) (hpl : Program.PlacedIn sbrdspT) :
    Init.SbrDspInitSpec X need := by
  intro R ra t hpre
  have h : t.dmem =⋆ (0x70 ?@ arg0 t ⋆ X) ⋆ Rest need R ra t :=
    pre_of_call (F := fun t => 0x70 ?@ arg0 t ⋆ X) hpre
  rw [Std.ExtHashMap.sep_assoc] at h
  obtain ⟨-, bs, hb, hm⟩ := Block.sep_elim h
  have hm' : t.dmem =⋆ (bs =@ arg0 t ⋆ X) ⋆ Rest need R ra t := by
    rw [Std.ExtHashMap.sep_assoc]; exact hm
  exact eventually_weaken _ _ _ _ (fun st ⟨ha, hq⟩ => ⟨ha, wSlots, wSlots_ok, hq⟩)
    (sbrdsp_pair X need hpl (R, bs) ra t ⟨hb, hm'⟩)

end Kraken.Examples.Sbr.WitEnv
