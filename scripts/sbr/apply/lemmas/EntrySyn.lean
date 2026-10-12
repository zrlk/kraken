set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Syn helper lemmas (apply) -/

/-- Re-packing the footprint at values `y` (that `Keep` the pointers of `x`) as `ApplyFPost`. -/
theorem fpost_of {e : Env} {x y : Args} {t : MachineData} {A K : Mem 64 → Prop} {m : Mem 64}
    (hK : x.Keep y) (h : m =⋆ A ⋆ (ApplyF e y t ⋆ K)) : m =⋆ A ⋆ (ApplyFPost e x t ⋆ K) := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu', hi', hc, hd⟩ := h
  obtain ⟨-, -, hf, he, -, ha', hs, hr, hD⟩ := hK
  exact ⟨a, b, hu, hi, ha, c, d, hu', hi', ⟨y, he, hf, ha', hs, hr, hD, hc⟩, hd⟩


/-- The callees' area with four 8-byte cells (the stack arguments of `sbr_qmf_synthesis`) carved off its top. -/
theorem res_args (k : Nat) (hk : k ≤ 2 ^ 32) (r : BitVec 64) (K : Mem 64 → Prop) :
    Reserve (0x298 + k) r ⋆ K
      = 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ (8 ?@ (r - 24#64) ⋆ (8 ?@ (r - 32#64)
        ⋆ (Reserve (0x278 + k) (r - 32#64) ⋆ K)))) := by
  rw [show 0x298 + k = 8 + (8 + (8 + (8 + (0x278 + k)))) by omega,
    Reserve_split 8 _ r (by omega)]
  rw [Reserve_split 8 _ (r - BitVec.ofNat 64 8) (by omega)]
  rw [Reserve_split 8 _ (r - BitVec.ofNat 64 8 - BitVec.ofNat 64 8) (by omega)]
  rw [Reserve_split 8 _ (r - BitVec.ofNat 64 8 - BitVec.ofNat 64 8 - BitVec.ofNat 64 8) (by omega)]
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Std.ExtHashMap.sep_assoc]

/-- A raw 4-byte block holds some 32-bit value. -/
theorem blk4_cell {a : BitVec 64} {F : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ 4 ?@ a ⋆ F) :
    ∃ v : BitVec 32, m =⋆ cell4 a v ⋆ F := by
  obtain ⟨-, bs, hl, h⟩ := Block.sep_elim h
  refine ⟨BitVec.ofInt 32 (Int.ofBytes bs), ?_⟩
  have e : Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt = bs := by
    rw [BitVec.toInt_ofInt, ← Int.toBytes_emod, Int.take]
    have h2 : (Int.ofBytes bs).bmod (2 ^ 32) % (2 ^ (8 * 4) : Int) = Int.ofBytes bs % 2 ^ (8 * 4) :=
      Int.bmod_emod
    rw [h2, show Int.ofBytes bs % 2 ^ (8 * 4) = (Int.ofBytes bs).take (8 * 4) from rfl, Int.toBytes_emod,
      Int.toBytes_ofBytes 4 bs (by omega), List.take_of_length_le (by omega)]
  simp only [cell4, Val, e]
  exact h

/-- The callees' area at the `sbr_qmf_synthesis` calls (stack arguments already pushed):
the return-address slot, the callee's `qmfNeed k`, the rest. -/
theorem res_qmf (k : Nat) (hk : k ≤ 2 ^ 32) (r : BitVec 64) (K : Mem 64 → Prop) :
    Reserve (0x278 + k) r ⋆ K
      = 8 ?@ (r - 8#64) ⋆ (Reserve (0x130 + k) (r - 8#64)
        ⋆ (0x140 ?@ (r - BitVec.ofNat 64 (0x278 + k)) ⋆ K)) := by
  rw [show 0x278 + k = 8 + (0x270 + k) by omega, Reserve_split 8 (0x270 + k) r (by omega),
    Reserve.excess (0x130 + k) (0x270 + k) (r - BitVec.ofNat 64 8) (by omega) (by omega),
    BitVec.sub_sub_ofNat, show 0x270 + k - (0x130 + k) = 0x140 by omega]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The pushed `div` (0 or 1, 8 bytes): its low 4 bytes as `sbr_qmf_synthesis` reads them, the high 4. -/
theorem c8_div (a : BitVec 64) (d : Nat) (hd : d ≤ 1) :
    c8 a (BitVec.ofNat 64 d) = Int.toBytes 4 (d : Int) =@ a ⋆ Int.toBytes 4 0 =@ (a + 4#64) := by
  have e : Int.toBytes 8 (BitVec.ofNat 64 d).toInt = Int.toBytes 4 (d : Int) ++ Int.toBytes 4 0 := by
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> decide
  simp only [c8, e]
  exact Val.append_eq _ _ _ _ (by simp only [Int.toBytes_length]; try rfl) (by simp only [Int.toBytes_length]; try decide)

theorem syn_al32 (a : BitVec 64) (c : Nat) (ha : isAligned 32 a = true) (hc : c % 32 = 0) :
    isAligned 32 (a + BitVec.ofNat 64 c) = true :=
  isAligned_add (by decide) ha (by simp only [BitVec.toNat_ofNat]; omega)

theorem syn_al16 {a : BitVec 64} (h : isAligned 32 a = true) : isAligned 16 a = true := by
  simp only [isAligned, beq_iff_eq] at *; omega

/-- `rsp` arithmetic at the call: `a - c + d = a - (c - d)`. -/
theorem syn_subadd (a : BitVec 64) (c d : Nat) (h : d ≤ c) (hc : c < 2 ^ 64) :
    a - BitVec.ofNat 64 c + BitVec.ofNat 64 d = a - BitVec.ofNat 64 (c - d) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- The `sbr_qmf_synthesis` contract at `div = dsN x`. -/
theorem syn_qspec {k : Nat} {e : Env} {x : Args} (h0 : QmfSynthesisSpec 0 k e.Ctx e.TxTab e.fs.qfs)
    (h1 : QmfSynthesisSpec 1 k e.Ctx e.TxTab e.fs.qfs) :
    QmfSynthesisSpec (dsN x) k e.Ctx e.TxTab e.fs.qfs := by
  unfold dsN; split <;> assumption

theorem syn_dsN_le (x : Args) : dsN x ≤ 1 := by unfold dsN; split <;> omega

theorem syn_win0 {x : Args} (h : dsN x = 0) :
    (2560 ?@ lab "sbr_qmf_window_us" : Mem 64 → Prop) = (2560 >>> dsN x) ?@ qmfWin (dsN x) := by
  rw [h]; simp only [qmfWin, if_true, Nat.reduceShiftRight]

theorem syn_win1 {x : Args} (h : dsN x = 1) :
    (1280 ?@ lab "sbr_qmf_window_ds" : Mem 64 → Prop) = (2560 >>> dsN x) ?@ qmfWin (dsN x) := by
  rw [h]; simp only [qmfWin, Nat.one_ne_zero, if_false, Nat.reduceShiftRight]

/-! ### D6 (M4b, apply-dqcpl): the `ff_ps_apply` call (`L9a02`) -/

/-- D6: `PsWF` after `ff_ps_apply`: `psc` unchanged, the new `h'` within W6. -/
theorem ps_wf_post {c h h' : List UInt8} (hw : PsWF c h) (hl : h'.length = 68)
    (h6 : ∀ b < 34, 0 ≤ i8 h' b ∧ i8 h' b ≤ 63 ∧ 0 ≤ i8 h' (34 + b) ∧ i8 h' (34 + b) ≤ 63) :
    PsWF c h' := by
  obtain ⟨a1, -, a3, a4, a5, a6, a7, a8, -, a10⟩ := hw
  exact ⟨a1, hl, a3, a4, a5, a6, a7, a8, h6, a10⟩

/-- D6: `SbrWF` with the new phase histories. -/
theorem ps_sbrwf_post {y : Args} {h' : List UInt8} (hw : SbrWF y) (hl : h'.length = 68)
    (h6 : ∀ b < 34, 0 ≤ i8 h' b ∧ i8 h' b ≤ 63 ∧ 0 ≤ i8 h' (34 + b) ∧ i8 h' (34 + b) ≤ 63) :
    SbrWF { y with psh := h' } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hw
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, ps_wf_post a16 hl h6⟩

/-- D6: `Int.ofBytes` is the unsigned value. -/
theorem ps_int_ofBytes (bs : List UInt8) : Int.ofBytes bs = ((Nat.ofBytes bs : Nat) : Int) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Int.ofBytes bs * 256 + ((b.toNat : Nat) : Int) = ((Nat.ofBytes bs * 256 + b.toNat : Nat) : Int)
    rw [ih]; omega

/-- D6: the gate `ps->common.start != 0` read as a 32-bit load. -/
theorem ps_gate {bs : List UInt8} (h : BitVec.ofInt 32 (Int.ofBytes bs) ≠ 0) :
    (BitVec.ofNat 32 (Nat.ofBytes bs)).toInt ≠ 0 := by
  rw [ps_int_ofBytes, BitVec.ofInt_natCast] at h
  intro h'; apply h; apply BitVec.eq_of_toInt_eq; rw [h']; simp

/-- D6: the gate from `cmpl $0x0, (ps)` / `je` not taken. -/
theorem ps_gate2 {bs : List UInt8} {v : Int} (hv : some (Int.ofBytes bs) = some v)
    {f : StatusFlags.from_result.Remaining}
    (h : CondCode.z.interp (StatusFlags.from_result (BitVec.ofInt 32 v - BitVec.setWidth 32 0#64) f) = false) :
    (BitVec.ofNat 32 (Nat.ofBytes bs)).toInt ≠ 0 := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_eq_false_iff_ne, ne_eq] at h
  cases hv
  refine ps_gate fun h' => h ?_
  rw [h']; decide

/-- D6: `ps_post_ex` inside the call frame (`ra` cell, reserve). -/
theorem ps_post_ex3 {PsTab : Mem 64 → Prop} {a : PsArgs} {t : MachineData} {A B F : Mem 64 → Prop}
    {m : Mem 64} (h : m =⋆ A ⋆ (B ⋆ (PsApplyFPost PsTab a t ⋆ F))) :
    ∃ h' : List UInt8, h'.length = 68
      ∧ (∀ b < 34, 0 ≤ i8 h' b ∧ i8 h' b ≤ 63 ∧ 0 ≤ i8 h' (34 + b) ∧ i8 h' (34 + b) ≤ 63)
      ∧ (m =⋆ A ⋆ (B ⋆ (PsApplyF PsTab { a with psh := h' } t ⋆ F))) := by
  obtain ⟨m1, m2, hu, hi, hA, m3, m4, hu2, hi2, hB, m5, m6, hu3, hi3, ⟨h', hl, hw, hp⟩, hF⟩ := h
  exact ⟨h', hl, hw, m1, m2, hu, hi, hA, m3, m4, hu2, hi2, hB, m5, m6, hu3, hi3, hp, hF⟩

/-! ### M4b layout (apply-mapb): the synthesis call windows -/

/-- The rest of `analysis_filterbank_samples` beside the `qmfVSize` window of the
synthesis call (`a` = `&synthesis_filterbank_samples`): the last 3200 bytes when the window
is the larger one (11264 bytes), else all 5248 bytes. -/
def qvRest (dd : Nat) (off : BitVec 32) (a : BitVec 64) : Mem 64 → Prop :=
  if dd = 0 ∧ 1152 < off.toInt then 3200 ?@ (a + 11264#64) else 5248 ?@ (a + 9216#64)

omit [CodeEnv] in
/-- `synthesis_filterbank_samples ++ analysis_filterbank_samples` as the synthesis call's
`v0` window (`qmfVSize`) and the rest: for the larger window this is `a3_overread_carve` (relative to
`a = d + 0x80`). -/
theorem qv_carve (a : BitVec 64) (dd : Nat) (off : BitVec 32) (K : Mem 64 → Prop) :
    9216 ?@ a ⋆ (5248 ?@ (a + 9216#64) ⋆ K) = qmfVSize dd off ?@ a ⋆ (qvRest dd off a ⋆ K) := by
  unfold qmfVSize qvRest
  split
  · have e1 := Block.split a 9216 2048 (by decide)
    have e2 := Block.split (a + 9216#64) 2048 3200 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1 e2
    rw [e1, e2]
    simp only [Std.ExtHashMap.sep_assoc]
  · rfl
