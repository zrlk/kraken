import WeakCore.TermOverCrBII
import WeakCore.TermOverCr4
import WeakCore.TermOverCrH
import WeakCore.TermPredHold

/-! # TermOverCrProm: the credited cover after a promise step (M5)

`OpenOverCrProm` (TermOverCrBII).  Along a promise step of `j` (new message `n = c.mem.size`, top of
memory; plant at own private cells of `j`, `PlantSpec`):
* (A) another thread `i`: nothing changes at its own frontier cells but the extra foreign promise `n`
  (skipped above `i`'s lowest own promise, a non-`undef` message: `mem_promAt_above`); frame
  (`overCr_frameD`, no new item);
* (B1) `j` at an old frontier cell: frame, plus the item of `n` when `cr' n ≠ 0` (a plant credit after
  the step, `PromCrK`; the pool has no credit at `n`, `PoolTag`);
* (B2) `j` at a planted (formerly private) cell: nothing is overtaken (`OwnOKSF` with no frontier:
  every non-promise message there is at or below coherence, below every promise, `PromAbove`), old
  credits at non-word units are zero (`OldCr`; no `PlantCr` without a frontier; no pool tag without a
  footprint), so the items are at most that of `n`.
-/

namespace TermOverCrProm
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCr
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- An item of the credited cover. -/
abbrev Item := Ts × Nat × Ty × List Word × Res × (Nat → Bool)

/-- **Skipped above a non-`undef` message**: at a non-visible unit, an own or footprint promise above
a non-`undef` message of the unit is skipped (at a predicted unit the first write is at or below
that message). -/
theorem mem_promAt_above {E : TEnv} {s : St} {a : Address} {t tw : Ts} {mw : Msg}
    (hnv : ¬ VisU E a) (ht : t ∈ s.promises ++ FpAt E a) (hlt : tw < t)
    (hmw : s.mem[tw]? = some mw) (hl : mw.loc = a) (hu : mw.val ≠ .undef) :
    t ∈ PromAt E s a := by
  classical
  unfold PromAt
  simp only [hnv, ↓reduceIte]
  by_cases hpu : PredU E a
  · simp only [hpu, ↓reduceIte]
    obtain ⟨h, hf, hle⟩ := TermPredHold.firstW_ex tw mw hmw hl hu
    exact List.mem_filter.2 ⟨ht, decide_eq_true ⟨h, hf, Nat.lt_of_le_of_lt hle hlt⟩⟩
  · simp only [hpu, ↓reduceIte]
    exact ht

#print axioms mem_promAt_above

/-- A credited item only reads its holder's credit. -/
theorem crItemQ_cr {E : TEnv} {s : St} {cr cr2 : Ts → Res} {l : AllocLabel} {c : Cell} {x : Item}
    (h : CrItemQ E s cr l c x) (hle : cr x.1 ≤ cr2 x.1) : CrItemQ E s cr2 l c x := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hp⟩ := h
  exact ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, Res.le_trans a12 hle, hp⟩

#print axioms crItemQ_cr

/-- The cover's unit tests agree at a label where the environments agree. -/
theorem unit_congr {E E' : TEnv} {c : Cell} {l : AllocLabel} (hs : E'.sto l = E.sto l) (ht : E'.tid = E.tid)
    (hp : E'.pfr l = E.pfr l) (hi : E'.ini l = E.ini l) (hri : E'.rini l = E.rini l) (o : Nat) :
    (CovU E' c l o ↔ CovU E c l o) ∧ (VisU E' ⟨l, o⟩ ↔ VisU E ⟨l, o⟩) ∧ (PredU E' ⟨l, o⟩ ↔ PredU E ⟨l, o⟩) := by
  have hrc : E'.rc l = E.rc l := TEnv.rc_congr hi hri
  have hPU : PredU E' ⟨l, o⟩ ↔ PredU E ⟨l, o⟩ := PredU_congr hs ht hp hi hrc
  refine ⟨?_, VisU_congr hs ht hp, hPU⟩
  have hIR : InitRr E' c l o ↔ InitRr E c l o := by
    unfold InitRr; rw [hrc]
  exact ⟨fun h => h.imp hIR.1 hPU.1, fun h => h.imp hIR.2 hPU.2⟩

#print axioms unit_congr

/-! ## The frame, with new items -/

section frame
variable {s s' : St}
  (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
  (hpr : ∀ t, t ∈ s.promises → t ∈ s'.promises)
  (hnew : ∀ t, t ∈ s'.promises → t ∉ s.promises → s.mem.size ≤ t)
  (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
include hpre hpr hnew hP

/-- **The credited cover is kept, new items appended** (`overCr_frame` with the overtaking premise
only at non-visible units, credits compared only at non-word holders, and new items `D` at new
promises covering the new credited promises). -/
theorem overCr_frameD {E E' : TEnv} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell} {D : List Item}
    (hTop : ∀ t, t ∈ s'.promises → t ∉ s.promises → ∀ t' m, t < t' → s'.mem[t']? = some m →
      m.loc.label ≠ l)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hcr : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr t ≤ cr' t)
    (hI : ∀ o, CovU E' c l o → CovU E c l o)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, WinG E' s' l o tw → WinG E s l o tw)
    (hO : ∀ o tw, ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      TermPlant.OverT E s ⟨l, o⟩ tw)
    (hcr0 : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr' t ≠ .zero → (t ∈ s.promises ∧ cr t ≠ .zero) ∨ t ∈ D.map (·.1))
    (hDn : (D.map (·.1)).Nodup) (hDo : ∀ x ∈ D, x.1 ∉ s.promises)
    (hDi : ∀ x ∈ D, CrItemQ E' s' cr' l c x)
    (hDw : ∀ x ∈ D, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0)
    (hDH : HolderLow s' l D)
    (h : OverCrE E s cr l c) : OverCrE E' s' cr' l c := by
  obtain ⟨Gs, ⟨hnd, hit, hcov, hwa, hz⟩, hHL⟩ := h
  have hHL' : HolderLow s' l Gs := holderLow_tr (fun t m _ hin hm => by rw [← hpre t (hP t hin)]; exact hm)
    (fun t ht hin x hx => by
      obtain ⟨_mh0, _us0, _hm0, _hl0, hlo0, _⟩ := hit x hx
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le (hP _ hlo0.1) (hnew t ht hin))) hHL
  have hGo : ∀ x ∈ Gs, x.1 ∈ s.promises := fun x hx => by
    obtain ⟨_mh0, _us0, _hm0, _hl0, hlo0, _⟩ := hit x hx
    exact hlo0.1
  refine ⟨Gs ++ D, ⟨?_, fun x hx => ?_, fun o tw hi hv hl hg hov => ?_, fun x hx usS i o h1 h2 h3 => ?_,
    fun t m ht hm hl hw hnz => ?_⟩, holderLow_append hHL' hDH⟩
  · rw [List.map_append]
    refine List.nodup_append.2 ⟨hnd, hDn, ?_⟩
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact hDo y hy (hab ▸ hGo x hx)
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨mh, _us1, hm1, hlab1, hlo1, hnw1, _⟩ := hit x hx
      exact crItemQ_cr (crItem_frame hpre hpr hnew hP hsto hV (fun t _ => Res.le_refl (cr t)) (hwa x hx) hPU
        (hit x hx)) (hcr x.1 mh hlo1.1 hm1 hlab1 hnw1)
    · exact hDi x hx
  · by_cases hin : tw ∈ s.promises
    · have hl0 := lowOwn_back hpre hpr hP hl hin
      obtain ⟨x, hx, rest⟩ := hcov o tw (hI o hi) (hVU o hv) hl0 (hG o tw hg) (hO o tw hv hl0 hov)
      exact ⟨x, List.mem_append_left _ hx, rest⟩
    · obtain ⟨t', m, hlt, hm, hloc, -⟩ := hov
      exact absurd (by rw [hloc]) (hTop tw hl.1 hin t' m hlt hm)
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨t0, h0⟩ := hwa x hx usS i o h1 h2 h3
      exact ⟨t0, lowOwn_fwd hpre hpr hnew hP h0⟩
    · exact hDw x hx usS i o h1 h2 h3
  · have hw0 : ¬ WordUnit E m.loc := fun hw0 => hw ((WordUnit_congr (by rw [hl]; exact hsto)).2 hw0)
    rw [List.map_append]
    rcases hcr0 t m ht hm hl hw0 hnz with ⟨hin, hnz0⟩ | hD
    · exact List.mem_append_left _ (hz t m hin (by rw [← hpre t (hP t hin)]; exact hm) hl hw0 hnz0)
    · exact List.mem_append_right _ hD

#print axioms overCr_frameD

end frame

/-! ## Local facts -/

/-- `PromAt` grows along a step adding promises and footprint promises, agreeing on the unit
tests, with the first writes kept. -/
theorem promAt_mono {E E' : TEnv} {s s' : St} {a : Address} {t : Ts}
    (hVU : VisU E' a ↔ VisU E a) (hPU : PredU E' a ↔ PredU E a)
    (hpr : ∀ t, t ∈ s.promises → t ∈ s'.promises) (hfp : ∀ t, t ∈ FpAt E a → t ∈ FpAt E' a)
    (hab : ∀ t, AboveFW s.mem a t → AboveFW s'.mem a t)
    (h : t ∈ PromAt E s a) : t ∈ PromAt E' s' a := by
  classical
  have hsub : t ∈ s.promises ++ FpAt E a → t ∈ s'.promises ++ FpAt E' a := fun h' => by
    rcases List.mem_append.1 h' with h' | h'
    · exact List.mem_append_left _ (hpr t h')
    · exact List.mem_append_right _ (hfp t h')
  unfold PromAt at h ⊢
  by_cases hv : VisU E a
  · simp only [hv, ↓reduceIte] at h
    exact absurd h (List.not_mem_nil (a := t))
  · have hv' : ¬ VisU E' a := fun h' => hv (hVU.1 h')
    simp only [hv, hv', ↓reduceIte] at h ⊢
    by_cases hq : PredU E a
    · have hq' := hPU.2 hq
      simp only [hq, hq', ↓reduceIte] at h ⊢
      obtain ⟨h1, h2⟩ := List.mem_filter.1 h
      exact List.mem_filter.2 ⟨hsub h1, decide_eq_true (hab t (of_decide_eq_true h2))⟩
    · have hq' : ¬ PredU E' a := fun h' => hq (hPU.1 h')
      simp only [hq, hq', ↓reduceIte] at h ⊢
      exact hsub h

#print axioms promAt_mono

/-- **At an own cell without a frontier, a non-promise message is at or below coherence**
(`OwnOKSF`: `LatestSF` with no frontier; the message lies within the cell's words). -/
theorem priv_le_coh {g : G} {E : TEnv} {s : St} {l : AllocLabel} {cl : Cell} {t : Ts} {m : Msg}
    (hm : MemInv g E s) (hsto : E.sto l = some cl) (ho : cl.owner = some E.tid) (hpf : E.pfr l = none)
    (hw : InWords cl.ty m.loc.offset) (ht : t ∉ s.promises) (hmt : s.mem[t]? = some m)
    (hl : m.loc.label = l) : t ≤ s.vs.coh m.loc := by
  obtain ⟨vals, hc, hlat, -⟩ := hm.2.1 l cl hsto ho
  have hlen : m.loc.offset < vals.length := by
    rcases hc with ⟨hwc, -⟩ | ⟨N, e, us, hT, hus, -, hlen, -⟩
    · cases hA : accs cl.ty with
      | none => simp [wc, hA] at hwc
      | some L =>
        rw [wc_of_accs hA] at hwc
        have e1 := Option.some.inj hwc
        rw [← e1]
        exact hw.1 L hA
    · rw [hlen]; exact hw.2 N e us hT hus
  have hL := hlat m.loc.offset _ (List.getElem?_eq_getElem hlen)
  rw [hpf] at hL
  have ha : (⟨l, m.loc.offset⟩ : Address) = m.loc := by subst hl; rfl
  rw [ha] at hL
  refine Nat.le_of_not_lt fun hlt => ?_
  rcases hL.2.2 t m hlt hmt rfl with h | h
  · exact ht h
  · exact h.1 rfl

#print axioms priv_le_coh

section plant
variable {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}

theorem EgP_pfr_none {l : AllocLabel} (e : P l = none) : (EgP Eg P N j n).pfr l = Eg.pfr l := by
  simp only [EgP, GEnv.withFp, plantG, e]

theorem EgP_ini_none {l : AllocLabel} (e : P l = none) : (EgP Eg P N j n).ini l = Eg.ini l := by
  simp only [EgP, GEnv.withFp, plantG, e]

theorem EgP_fp (i : Nat) : (EgP Eg P N j n).fpOf i = fpProm Eg j n i := rfl

theorem EgP_sto : (EgP Eg P N j n).sto = Eg.sto := rfl

/-- A frontier is kept by the plant (`PlantSpec`: planted labels had none). -/
theorem EgP_pfr_some (hspec : PlantSpec Eg P j n) {l : AllocLabel} {f : Ts} (hf : Eg.pfr l = some f) :
    (EgP Eg P N j n).pfr l = some f := by
  cases e : P l with
  | none => rw [EgP_pfr_none e]; exact hf
  | some f' => rw [(hspec l f' e).1] at hf; cases hf

/-- A planted label is the promiser's cell, so at another thread's own cell nothing is planted. -/
theorem plant_none_of_own (hspec : PlantSpec Eg P j n) {l : AllocLabel} {cl : Cell} {i : Nat}
    (hcl : Eg.sto l = some cl) (ho : cl.owner = some i) (hij : i ≠ j) : P l = none := by
  cases e : P l with
  | none => rfl
  | some f =>
    obtain ⟨c1, hc1, ho1⟩ := (hspec l f e).2.1
    rw [hcl] at hc1; cases hc1
    rw [ho] at ho1; cases ho1
    exact absurd rfl hij

/-- Values transfer to the planted cut (`ValOfR_mono`). -/
theorem valOfR_EgP (hspec : PlantSpec Eg P j n) {i : Nat} {S : AllocLabel → Prop} {T : Ty} {ws : List Word}
    {R : Res} (h : ValOfR (Cut Eg i S) T ws R) : ValOfR (Cut (EgP Eg P N j n) i S) T ws R := by
  have hpf : ∀ l f, Eg.pfr l = some f → (EgP Eg P N j n).pfr l = some f := fun l f hf => EgP_pfr_some hspec hf
  refine ValOfR_mono (η₁ := Cut Eg i S) (η₂ := Cut (EgP Eg P N j n) i S) rfl rfl (fun l c hc => ?_) (fun l => plantG_ini_le Eg P N l) h hpf (fun _ _ h => h)
    (fun _ => Nat.le_refl _)
  obtain ⟨h1, h2⟩ := cutSto_some.1 hc
  exact cutSto_some.2 ⟨h1, h2.imp id fun ⟨f, hf⟩ => ⟨f, hpf l f hf⟩⟩

#print axioms valOfR_EgP

end plant

/-- A plant credit does not read the cut's `seen` set. -/
theorem plantCr_cutS {X : GEnv} {i : Nat} {S1 S2 : AllocLabel → Prop} {s : St} {m : Msg} {t : Ts} {R : Res}
    (h : PlantCr (Cut X i S1) s m t R) : PlantCr (Cut X i S2) s m t R := by
  obtain ⟨c, sb, S0, b0, S, us, wb, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  refine ⟨c, sb, S0, b0, S, us, wb, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, ?_⟩
  rcases a16 with ⟨K, ws, R0, b1, b2, b3, b4⟩ | hz
  · exact .inl ⟨K, ws, R0, b1, b2, b3, b4⟩
  · exact .inr hz

#print axioms plantCr_cutS

/-! ## The new promise's item -/

/-- **The item of the new promise `n`** (the top message): if `n` carries a nonzero credit at a
non-word unit of `l`, it is a plant credit (`PromCrK`), hence a credited item with the empty unit mask,
holder lowest in its piece (every promise is at most `n`, the window bound). -/
theorem newD_ex {Eg' : GEnv} {j : Nat} {S S2 : AllocLabel → Prop} {s' : St} {l : AllocLabel} {cl : Cell}
    {cr2 db2 cv : Ts → Res} {n : Ts}
    (hK : TermPlant.PromCrK (Cut Eg' j S2) s' cr2 db2) (hn : n ∈ s'.promises) (hsz : s'.mem.size = n + 1)
    (hplt : ∀ t, t ∈ s'.promises → t < s'.mem.size)
    (hcl : (Cut Eg' j S).sto l = some cl) (hcv : cr2 n ≤ cv n) :
    ∃ D : List Item, (D.map (·.1)).Nodup ∧ (∀ x ∈ D, x.1 = n) ∧ (∀ x ∈ D, CrItemQ (Cut Eg' j S) s' cv l cl x) ∧
      (∀ x ∈ D, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
        ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0) ∧ HolderLow s' l D ∧
      (∀ m, s'.mem[n]? = some m → m.loc.label = l → ¬ WordUnit (Cut Eg' j S) m.loc → cr2 n ≠ .zero →
        n ∈ D.map (·.1)) := by
  classical
  by_cases hc : ∃ m, s'.mem[n]? = some m ∧ m.loc.label = l ∧ ¬ WordUnit (Cut Eg' j S) m.loc ∧ cr2 n ≠ .zero
  · obtain ⟨m, hm, hl, hnw, hnz⟩ := hc
    have hP : PlantCr (Cut Eg' j S) s' m n (cr2 n) :=
      plantCr_cutS (TermOverCr4.plantCr_of_nz hK hn hm (fun h => hnw h) hnz)
    obtain ⟨c1, sb, S0, b0, Sx, us, wb, hsto1, -, -, hseg, hat, hSol, hnw1, hus, hn0, h1, h2, htw, hwb, -, hlow,
      hK1⟩ := hP
    rw [hl, hcl] at hsto1
    obtain rfl : cl = c1 := Option.some.inj hsto1
    rcases hK1 with ⟨K, ws, R0, hlen, hv, hR0, -⟩ | hz
    · have hlowP : ∀ t' m', t' ∈ s'.promises → s'.mem[t']? = some m' → m'.loc.label = l →
          sb + b0 ≤ m'.loc.offset → m'.loc.offset < sb + b0 + nWords us → n ≤ t' :=
        fun t' m' ht hm' hl' h1' h2' => hlow t' m' ht hm' (hl'.trans hl.symm) h1' h2'
          (show t' ≤ wb by have h3 := hplt t' ht; rw [hsz] at h3; exact Nat.le_trans (Nat.le_of_lt_succ h3) htw)
      have hLO : TermPlant.LowOwn s' m.loc n := ⟨hn, ⟨m, hm, rfl⟩, fun t' m' ht hm' hloc =>
        hlowP t' m' ht hm' (by rw [hloc]; exact hl) (by rw [hloc]; exact h1) (by rw [hloc]; exact h2)⟩
      have hI := item_of_plantCr (c := cl) (K := fun _ => false) (wb := wb) (cr := cv) hm hseg hat hSol hnw1 hus
        hn0 h1 h2 hlen hv hR0 (fun i o w t' hK => absurd hK (by simp)) hLO hcv
        (fun i o tw' hK => absurd hK (by simp))
      rw [hl] at hI
      refine ⟨[(n, sb + b0, Sx, ws, R0, fun _ => false)], by simp, fun x hx => ?_,
        fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun _ _ _ _ _ => by simp⟩
      · rw [List.mem_singleton.1 hx]
      · rw [List.mem_singleton.1 hx]; exact crItemQ_of hI
      · rw [List.mem_singleton.1 hx]
        intro usS i o _ hK
        simp at hK
      · rw [List.mem_singleton.1 hx]
        intro usS hus' t m' ht hm' hl' h1' h2'
        rw [hus] at hus'
        obtain rfl : us = usS := Option.some.inj hus'
        exact hlowP t m' ht hm' hl' h1' h2'
    · exact absurd hz hnz
  · refine ⟨[], by simp, by simp, by simp, by simp, fun x hx => absurd hx (List.not_mem_nil (a := x)),
      fun m hm hl hnw hnz => absurd ⟨m, hm, hl, hnw, hnz⟩ hc⟩

#print axioms newD_ex

/-! ## (A) another thread -/

section main
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **(A) Another thread's own frontier cell after a promise step**: frame, no new item. -/
theorem overCr_prom_other {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {cv : Nat → Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hspec : PlantSpec Eg P j c.mem.size)
    (hOC : OverCrG Eg c cv)
    {i : Nat} {thi : TTh} (hij : i ≠ j) (hthi : c.ths[i]? = some thi) (S : AllocLabel → Prop) {l : AllocLabel}
    {cl : Cell} (hcl : Eg.sto l = some cl) (ho : cl.owner = some i)
    (hpf : (EgP Eg P N j c.mem.size).pfr l ≠ none) :
    OverCrE (Cut (EgP Eg P N j c.mem.size) i S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thi) (cv i) l cl := by
  classical
  have e : P l = none := plant_none_of_own hspec hcl ho hij
  have hpf0 : Eg.pfr l ≠ none := by rwa [EgP_pfr_none e] at hpf
  have hold := hOC i thi S hthi l cl (cutSto_own hcl ho) ho hpf0
  have hs : (Cut (EgP Eg P N j c.mem.size) i S).sto l = (Cut Eg i S).sto l := by
    show cutSto _ i l = cutSto Eg i l
    rw [cutSto_own (Eg := EgP Eg P N j c.mem.size) hcl ho, cutSto_own hcl ho]
  have hU := unit_congr (E := Cut Eg i S) (E' := Cut (EgP Eg P N j c.mem.size) i S) (c := cl) hs rfl
    (EgP_pfr_none (N := N) (j := j) (n := c.mem.size) e) (EgP_ini_none (N := N) (j := j) (n := c.mem.size) e) rfl
  have hVis : Vis (Cut (EgP Eg P N j c.mem.size) i S) l ↔ Vis (Cut Eg i S) l := Vis_congr hs rfl (EgP_pfr_none (N := N) (j := j) (n := c.mem.size) e)
  have hfp0 : ∀ o t, t ∈ FpAt (Cut Eg i S) ⟨l, o⟩ → t ∈ FpAt (Cut (EgP Eg P N j c.mem.size) i S) ⟨l, o⟩ := by
    intro o t ht
    unfold FpAt at ht ⊢
    by_cases hv : Vis (Cut Eg i S) l
    · simp only [hv, hVis.2 hv, ↓reduceIte] at ht ⊢
      show t ∈ fpProm Eg j c.mem.size i
      simp only [fpProm, hij, ↓reduceIte]
      exact List.mem_append_left _ ht
    · simp only [hv, ↓reduceIte] at ht
      exact absurd ht (List.not_mem_nil (a := t))
  have hpre : ∀ t, t < (stOf c.mem c.pairs thi).mem.size →
      (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thi).mem[t]? = (stOf c.mem c.pairs thi).mem[t]? :=
    fun t ht => push_lt ht
  have hnew : ∀ t, t ∈ (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thi).promises →
      t ∉ (stOf c.mem c.pairs thi).promises → (stOf c.mem c.pairs thi).mem.size ≤ t :=
    fun t h1 h2 => absurd h1 h2
  refine overCr_frameD (D := []) hpre (fun t h => h) hnew (fun t ht => X.inv.plt i thi t hthi ht)
    (fun t h1 h2 => absurd h1 h2) hs (fun S ws R0 h => valOfR_EgP hspec h)
    (fun t m _ _ _ _ => Res.le_refl _) (fun o h => ((hU o).1).1 h) (fun o h h' => h (((hU o).2.1).2 h'))
    (fun o h => ((hU o).2.2).2 h)
    (fun o tw h => TermOverCrW.winG_back hpre hnew (fun _ => Nat.le_refl _) (fun t _ ht => hfp0 0 t ht) h)
    (fun o tw hv hl hov => ?_) (fun t m ht _ _ _ hnz => .inl ⟨ht, hnz⟩) (by simp) (by simp) (by simp) (by simp)
    (fun x hx => absurd hx (List.not_mem_nil (a := x))) hold
  obtain ⟨t, m, hlt, hm, hloc, hnp⟩ := hov
  have hsz : t < c.mem.size + 1 := by
    have h := TermPiece.lt_size_of_some (mem := c.mem.push ⟨a, v, w⟩) hm
    rw [Array.size_push] at h
    exact h
  obtain ⟨htw, ⟨mw, hmw, hlw⟩, -⟩ := hl
  by_cases htn : t < c.mem.size
  · refine ⟨t, m, hlt, (push_lt htn).symm.trans hm, hloc, fun hin => hnp ?_⟩
    exact promAt_mono (s := stOf c.mem c.pairs thi) (s' := stOf (c.mem.push ⟨a, v, w⟩) c.pairs thi) ((hU o).2.1) ((hU o).2.2) (fun t h => h) (hfp0 o) (fun t h => AboveFW_pushM (M := c.mem) _ h) hin
  · exfalso
    have e2 : t = c.mem.size := Nat.le_antisymm (Nat.le_of_lt_succ hsz) (Nat.le_of_not_lt htn)
    subst e2
    apply hnp
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpf
    have hvis : Vis (Cut (EgP Eg P N j c.mem.size) i S) l := Vis_pfr (E := Cut (EgP Eg P N j c.mem.size) i S) hf
    refine mem_promAt_above hv (List.mem_append_right _ ?_) hlt
      ((push_lt (X.inv.plt i thi tw hthi htw)).trans hmw) hlw (X.inv.promNU i thi tw mw hthi htw hmw)
    unfold FpAt
    simp only [hvis, ↓reduceIte]
    show c.mem.size ∈ fpProm Eg j c.mem.size i
    simp [fpProm, hij]

#print axioms overCr_prom_other

/-! ## (B) the promiser -/

/-- **(B) The promiser's own frontier cell after its promise**: at an old frontier cell the frame
plus the new promise's item; at a planted cell, from scratch (nothing overtaken, no old credit at a
non-word unit). -/
theorem overCr_prom_self {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {pl : Nat → Ts → Res} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hspec : PlantSpec Eg P j c.mem.size)
    (hOC : OverCrG Eg c (crPl cr pl)) (hPT : PoolTag Eg c pl)
    (hcr : ∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop, ¬ WordUnit (Cut Eg j S) m.loc →
      cr' t = cr j t)
    (hS : ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
      (EgP Eg P N j c.mem.size) (Tot j) HP' HS' cr' db')
    (S : AllocLabel → Prop) {l : AllocLabel} {cl : Cell} (hcl : Eg.sto l = some cl) (ho : cl.owner = some j)
    (hpf : (EgP Eg P N j c.mem.size).pfr l ≠ none) :
    OverCrE (Cut (EgP Eg P N j c.mem.size) j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size))
      (fun t => cr' t + pl j t) l cl := by
  classical
  have hplt : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  have hnin : c.mem.size ∉ th.promises := fun h => Nat.lt_irrefl _ (hplt _ h)
  have hnP : c.mem.size ∈ (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).promises :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hsz : (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).mem.size = c.mem.size + 1 :=
    Array.size_push _
  have hplt' : ∀ t, t ∈ (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).promises →
      t < (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).mem.size := fun t ht => by
    rw [hsz]
    rcases List.mem_append.1 ht with h | h
    · exact Nat.lt_succ_of_lt (hplt t h)
    · rw [List.mem_singleton.1 h]; exact Nat.lt_succ_self _
  have hpl : pl j c.mem.size = .zero := by
    by_cases hz : pl j c.mem.size = .zero
    · exact hz
    · exact absurd (hPT.1 j th _ X.hth hz).1 hnin
  obtain ⟨S2, -, -, -, -, -, hK⟩ := hS
  have hcl' : (Cut (EgP Eg P N j c.mem.size) j S).sto l = some cl := cutSto_own (Eg := EgP Eg P N j c.mem.size) hcl ho
  have hsEq : (Cut (EgP Eg P N j c.mem.size) j S).sto l = (Cut Eg j S).sto l := by
    rw [hcl']; exact (cutSto_own hcl ho).symm
  have hcv : cr' c.mem.size ≤ cr' c.mem.size + pl j c.mem.size := fun key => by
    rw [Res.add_apply]; exact Nat.le_add_right _ _
  obtain ⟨D, hDn, hD1, hDi, hDw, hDH, hDc⟩ := newD_ex (j := j) (S := S) (cv := fun t => cr' t + pl j t) hK hnP hsz
    hplt' hcl' hcv
  have hDo : ∀ x ∈ D, x.1 ∉ (stOf c.mem c.pairs th).promises := fun x hx => by
    rw [hD1 x hx]; exact hnin
  have hcrEq : ∀ t m, t ∈ th.promises → c.mem[t]? = some m → m.loc.label = l →
      ¬ WordUnit (Cut (EgP Eg P N j c.mem.size) j S) m.loc → cr' t = cr j t :=
    fun t m ht hm hl hw => hcr t m ht hm S (fun h => hw ((WordUnit_congr (by rw [hl]; exact hsEq)).2 h))
  have hpre : ∀ t, t < (stOf c.mem c.pairs th).mem.size →
      (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).mem[t]? = (stOf c.mem c.pairs th).mem[t]? :=
    fun t ht => push_lt ht
  -- the overtaking witness at a non-visible unit of `l` above an old lowest promise
  cases e : P l with
  | none =>
    have hpf0 : Eg.pfr l ≠ none := by rwa [EgP_pfr_none e] at hpf
    have hold := hOC j th S X.hth l cl (cutSto_own hcl ho) ho hpf0
    have hU := unit_congr (E := Cut Eg j S) (E' := Cut (EgP Eg P N j c.mem.size) j S) (c := cl) hsEq rfl
      (EgP_pfr_none (N := N) (j := j) (n := c.mem.size) e) (EgP_ini_none (N := N) (j := j) (n := c.mem.size) e) rfl
    have hfpEq : ∀ o, FpAt (Cut (EgP Eg P N j c.mem.size) j S) ⟨l, o⟩ = FpAt (Cut Eg j S) ⟨l, o⟩ := fun o =>
      FpAt_congr hsEq rfl (EgP_pfr_none (N := N) (j := j) (n := c.mem.size) e)
        (show fpProm Eg j c.mem.size j = Eg.fpOf j by simp [fpProm])
    have hnew : ∀ t, t ∈ (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).promises →
        t ∉ (stOf c.mem c.pairs th).promises → (stOf c.mem c.pairs th).mem.size ≤ t := fun t ht hin => by
      rcases List.mem_append.1 ht with h | h
      · exact absurd h hin
      · rw [List.mem_singleton.1 h]; exact Nat.le_refl _
    refine overCr_frameD (D := D) hpre (fun t h => List.mem_append_left _ h) hnew hplt
      (fun t ht hin t' m hlt hm => ?_) hsEq (fun S ws R0 h => valOfR_EgP hspec h)
      (fun t m ht hm hl hw => ?_) (fun o h => ((hU o).1).1 h) (fun o h h' => h (((hU o).2.1).2 h'))
      (fun o h => ((hU o).2.2).2 h)
      (fun o tw h => TermOverCrW.winG_back hpre hnew (fun _ => Nat.le_refl _)
        (fun t _ ht => by rw [hfpEq]; exact ht) h)
      (fun o tw hv hl hov => ?_) (fun t m ht hm hl hw hnz => ?_) hDn hDo hDi hDw hDH hold
    · -- hTop: the new promise is the top message
      exfalso
      have h1 := hnew t ht hin
      have h2 := hplt' t ht
      have h3 := TermPiece.lt_size_of_some hm
      rw [hsz] at h2 h3
      exact Nat.lt_irrefl t' (Nat.lt_of_lt_of_le h3 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt h1 hlt)))
    · -- hcr
      have hw' : ¬ WordUnit (Cut (EgP Eg P N j c.mem.size) j S) m.loc :=
        fun h => hw ((WordUnit_congr (by rw [hl]; exact hsEq)).1 h)
      show cr j t + pl j t ≤ cr' t + pl j t
      rw [hcrEq t m ht hm hl hw']
      exact Res.le_refl _
    · -- hO
      obtain ⟨t, m, hlt, hm, hloc, hnp⟩ := hov
      have hsz1 : t < c.mem.size + 1 := by
        have h := TermPiece.lt_size_of_some hm
        rw [hsz] at h
        exact h
      obtain ⟨htw, ⟨mw, hmw, hlw⟩, -⟩ := hl
      by_cases htn : t < c.mem.size
      · refine ⟨t, m, hlt, (push_lt htn).symm.trans hm, hloc, fun hin => hnp ?_⟩
        exact promAt_mono (s := stOf c.mem c.pairs th) (s' := stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size))
          ((hU o).2.1) ((hU o).2.2) (fun t h => List.mem_append_left _ h) (fun t h => by rw [hfpEq]; exact h)
          (fun t h => AboveFW_pushM (M := c.mem) _ h) hin
      · exfalso
        have e2 : t = c.mem.size := Nat.le_antisymm (Nat.le_of_lt_succ hsz1) (Nat.le_of_not_lt htn)
        subst e2
        exact hnp (mem_promAt_above hv (List.mem_append_left _ hnP) hlt
          ((push_lt (hplt tw htw)).trans hmw) hlw (X.inv.promNU j th tw mw X.hth htw hmw))
    · -- hcr0
      have hw' : ¬ WordUnit (Cut (EgP Eg P N j c.mem.size) j S) m.loc :=
        fun h => hw ((WordUnit_congr (by rw [hl]; exact hsEq)).1 h)
      rcases List.mem_append.1 ht with ht | ht
      · refine .inl ⟨ht, fun hz => hnz ?_⟩
        show cr' t + pl j t = .zero
        rw [hcrEq t m ht ((push_lt (hplt t ht)).symm.trans hm) hl hw']
        exact hz
      · have e2 := List.mem_singleton.1 ht
        subst e2
        refine .inr (hDc m hm hl hw' fun hz => hnz ?_)
        show cr' c.mem.size + pl j c.mem.size = .zero
        rw [hz, hpl]
        exact Res.add_zero _
  | some f =>
    have hpf0 : Eg.pfr l = none := (hspec l f e).1
    refine ⟨D, ⟨hDn, hDi, fun o tw hi hv hl hg hov => ?_, hDw, fun t m ht hm hl hw hnz => ?_⟩, hDH⟩
    · -- nothing is overtaken at a formerly private cell
      exfalso
      obtain ⟨t, m, hlt, hm, hloc, hnp⟩ := hov
      obtain ⟨htw, ⟨mw, hmw, hlw⟩, -⟩ := hl
      have hsz1 : t < c.mem.size + 1 := by
        have h := TermPiece.lt_size_of_some hm
        rw [hsz] at h
        exact h
      have htw' : tw ∈ th.promises := by
        rcases List.mem_append.1 htw with h | h
        · exact h
        · rw [List.mem_singleton.1 h] at hlt
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hsz1)) (Nat.lt_irrefl _)
      have hmw0 : c.mem[tw]? = some mw := (push_lt (hplt tw htw')).symm.trans hmw
      have hu := X.inv.promNU j th tw mw X.hth htw' hmw0
      by_cases hin : t ∈ (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)).promises ++
          FpAt (Cut (EgP Eg P N j c.mem.size) j S) ⟨l, o⟩
      · exact hnp (mem_promAt_above hv hin hlt hmw hlw hu)
      · have htp : t ∉ th.promises := fun h => hin (List.mem_append_left _ (List.mem_append_left _ h))
        have htn : t < c.mem.size := by
          refine Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hsz1) fun e2 => ?_
          subst e2
          exact hin (List.mem_append_left _ hnP)
        have hm0 : c.mem[t]? = some m := (push_lt htn).symm.trans hm
        obtain ⟨S0, -, -, hMI, -, -, -⟩ := X.inv.thr j th X.hth
        have hle := priv_le_coh (l := l) (cl := cl) hMI (cutSto_own hcl ho) ho hpf0
          (X.inv.msgWords t m cl hm0 (by rw [hloc]; exact hcl)) htp hm0 (by rw [hloc])
        have hpa := X.inv.promAbove j th X.hth tw htw' mw hmw0
        rw [hlw, ← hloc] at hpa
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle (Nat.lt_trans hpa hlt))
    · -- every credited promise of `l` at a non-word unit is the new one
      rcases List.mem_append.1 ht with ht | ht
      · exfalso
        apply hnz
        have hm0 : c.mem[t]? = some m := (push_lt (hplt t ht)).symm.trans hm
        have e1 := hcrEq t m ht hm0 hl hw
        obtain ⟨S0, -, -, -, -, -, hK0⟩ := X.inv.thr j th X.hth
        have hz1 : cr j t = .zero := by
          obtain ⟨m', hm', -, hc⟩ := hK0 t ht
          obtain rfl : m = m' := Option.some.inj (hm0.symm.trans hm')
          have hsEq0 : (Cut (EgP Eg P N j c.mem.size) j S).sto l = (Cut Eg (gOf p k arch c j).i S0).sto l := by
            rw [hcl']; exact (cutSto_own hcl ho).symm
          have hw0 : ¬ WordUnit (Cut Eg (gOf p k arch c j).i S0) m.loc :=
            fun h => hw ((WordUnit_congr (by rw [hl]; exact hsEq0)).2 h)
          rcases hc with hold | ⟨hpc, -⟩
          · exact TermOverCr4.oldCr_nword_zero hw0 hold
          · obtain ⟨_, _, _, _, _, _, _, -, -, hpf', -⟩ := hpc
            rw [hl] at hpf'
            exact absurd hpf0 hpf'
        have hz2 : pl j t = .zero := by
          by_cases hnz2 : pl j t = .zero
          · exact hnz2
          · exfalso
            obtain ⟨-, -, m', hm', hf, -⟩ := hPT.1 j th t X.hth hnz2
            obtain rfl : m = m' := Option.some.inj (hm0.symm.trans hm')
            rcases hf with hf | hf
            · obtain ⟨f1, mf, hf1, -⟩ := hf S
              have hnv : ¬ Vis (Cut Eg j S) m.loc.label := fun hv =>
                hv ⟨⟨cl, by rw [hl]; exact cutSto_own hcl ho, ho⟩, by rw [hl]; exact hpf0⟩
              unfold FpAt at hf1
              simp only [hnv, ↓reduceIte] at hf1
              exact absurd hf1 (List.not_mem_nil (a := f1))
            · -- the mask-free branch sits at a frontier label; `l` has none
              exact (hf S).1 (by rw [hl]; exact hpf0)
        show cr' t + pl j t = .zero
        rw [e1, hz1, hz2]
        exact Res.add_zero _
      · have e2 := List.mem_singleton.1 ht
        subst e2
        exact hDc m hm hl hw fun hz => hnz (by
          show cr' c.mem.size + pl j c.mem.size = .zero
          rw [hz, hpl]
          exact Res.add_zero _)

#print axioms overCr_prom_self

/-- **M5: `OpenOverCrProm` holds.** -/
theorem openOverCrProm_holds
    {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
    {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat} :
    TermOverCrBII.OpenOverCrProm p k arch Sp Init MintOK c0 plantOf plantN := by
  intro c Eg Tot HP HS cr db j th a v w pl X hspec hOC hPT HP' HS' cr' db' _hacct hcr hS i thi S hthi l cl hcl ho hpf
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [hpi.1]
  have hpairs : (promise c j a v w).pairs = c.pairs := by rw [hpi.1]
  rw [hmem, hpairs]
  have hcl0 : Eg.sto l = some cl :=
    cutSto_sub (Eg := EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (i := i) hcl
  by_cases hij : i = j
  · subst hij
    have e : thi = thP th c.mem.size := Option.some.inj (hthi.symm.trans hpi.2.1)
    subst e
    have hcv : crPl (upd cr i cr') pl i = fun t => cr' t + pl i t := by
      funext t; simp [crPl, upd]
    rw [hcv]
    exact overCr_prom_self X hspec hOC hPT hcr hS S hcl0 ho hpf
  · have hthi0 : c.ths[i]? = some thi := (TermStep.promise_other hij).symm.trans hthi
    have hcv : crPl (upd cr j cr') pl i = crPl cr pl i := by
      funext t; simp [crPl, upd, hij]
    rw [hcv]
    exact overCr_prom_other X hspec hOC hij hthi0 S hcl0 ho hpf

#print axioms openOverCrProm_holds

end main

end TermOverCrProm
