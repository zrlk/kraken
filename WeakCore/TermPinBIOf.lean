import WeakCore.TermMainDefs
import WeakCore.TermPinBI

/-! # TermPinBIOf — `bufInitHeld_of`: the ObligationsF field `bufInitHeld` as a theorem (PIN P8).

With `Rj' := Rj`, `SlotPayS` asks `Rj + Σ_F db ≤ Rj + Rv + Σ_F cr`, i.e. `Σ_F db ≤ Rv`: the holders' debits are paid by the
value the owner writes (`TermPinBI.dbF_le_val`). Memory's witness `Sp` is any list form of the cut's holding. -/

namespace TermPinBIOf
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The element type of a closed buffer cell type is closed. -/
theorem clo_elem {N : Nat} {e : Ty} (h : Clo (.array (.lit N) e)) : Clo e := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun ρ W x f => ?_⟩
  · simpa [tb] using h1
  · have := h2 ρ W x f
    simp only [cl] at this
    exact (Ty.array.inj this).2

/-- `wrapTop` of a buffer type is `wrapTop` of its element. -/
theorem wrapTop_elem {N : Nat} {e : Ty} (h : TermA4.wrapTop (.array (.lit N) e) = true) : TermA4.wrapTop e = true := h

/-- **`bufInitHeld` as a theorem.** -/
theorem bufInitHeld_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs) :
    ∀ x b ia v e, th.term = .let_ x (.bufInit b ia v) e →
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∃ Sp, TermStep.MemHeldL (CE η) (stOf c.mem c.pairs th) (HP i + HS) Sp ∧
          TermPlant.SlotPayS (CE η) (stOf c.mem c.pairs th) Sp (cr i) (db i) ad.label) := by
  intro x b ia v e _ rt w ad _ _ _
  obtain ⟨hCE, -, -, -, -, -, -⟩ := Y
  obtain ⟨S', -, -, -, hP, hSh, hC⟩ := X.inv.thr i th X.hth
  -- memory's holding at the cut, in list form; the cut's `S` only changes `seen`
  have hH : MemHeld (Cut Eg i S') (stOf c.mem c.pairs th) (HP i + HS) :=
    MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hP hSh
  have hH' : MemHeld (CE η) (stOf c.mem c.pairs th) (HP i + HS) := by
    rw [hCE]
    exact MemHeld_tr hH (fun _ => rfl) (fun _ => rfl) (fun l o w hl => by
      rwa [PromAt_congr (a := ⟨l, o⟩) rfl rfl rfl rfl rfl rfl]) id
  obtain ⟨Sp, hSp⟩ := hH'.toS
  refine ⟨Sp, hSp, ?_⟩
  -- the slot payment: `Rj' := Rj`, and the debits are paid by the written value
  intro cl N e' us F ws wq Rv Rj hsto hT hus hnw hF hws hwq hv hRj hvq hlat hFo
  refine ⟨Rj, hvq, ?_⟩
  have hsto' : Eg.sto ad.label = some cl := by
    have : (CE η).sto = cutSto Eg i := by rw [hCE]; rfl
    rw [this] at hsto
    exact cutSto_sub hsto
  have hwt : TermA4.wrapTop e' = true := by
    have := X.inv.stoW ad.label cl hsto'
    rw [hT] at this
    exact wrapTop_elem this
  have hclo : Clo e' := by
    have := StoClo_Cut X.inv.clo i S ad.label cl (by rw [← hCE]; exact hsto)
    rw [hT] at this
    exact clo_elem this
  have hmg : mg e' = true := GStoMg.elem X.inv.cmg hsto' hT
  obtain ⟨As, hA⟩ := TermPinAtoms.atomL_existsG e' (Or.inr ⟨hclo, hmg⟩) (by rw [hus]; simp)
  have hC' : TermPlant.PromCrK (CE η) (stOf c.mem c.pairs th) (cr i) (db i) := by rw [hCE]; exact hC
  have hle : Res.sum (F.map (db i)) ≤ Rv := by
    refine TermPinBI.dbF_le_val (mem := (stOf c.mem c.pairs th).mem) (j := (CE η).rc ad.label) hsto hT hus hA hwt hF hws hv (fun o t hFt => ?_)
    obtain ⟨htp, m, xw, hm, hx, hloc, hval, hw1, hfw⟩ := hFo o t hFt
    obtain ⟨m', hm', hd, -⟩ := hC' t htp
    rw [hm] at hm'; cases hm'
    exact ⟨m, xw, hm, hx, hloc, hval, hw1, hfw, hd⟩
  exact Res.le_def.2 fun key => by
    have h1 := Res.le_def.1 hle key
    simp only [Res.add_apply] at h1 ⊢
    omega

#print axioms TermPinBIOf.bufInitHeld_of

end TermPinBIOf
