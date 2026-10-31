/-
**The event layer** of `ThSys_plantW`: the promiser's `ThSysAt` at the unplanted
environment after its promise (E1), and the per-label plant hypotheses from the promise
context (E2).  Against the closure-fix chain.
-/
import WeakCore.TermPlantL
import WeakCore.TermInterf
namespace TermPlantE
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermMain TermPlantR TermPlantW TermPlantL
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-! ## (E1) The promise step at the unplanted environment -/

/-- `TermInterf.promSelfK_holds` without its (unused) no-plant and `ThSysAt` premises: the
promiser's plant credits survive its own promise (the new promise is above every window). -/
theorem promSelfK_any {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) :
    ∀ tw m, tw ∈ th.promises → c.mem[tw]? = some m →
      PlantCr (Cut Eg j S) (stOf c.mem c.pairs th) m tw (cr j tw) →
      PlantCr (Cut Eg j S) (promSt (stOf c.mem c.pairs th) a v w) m tw (cr j tw) := by
  intro tw m _ _ h
  have hPlt : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  obtain ⟨c1, sb, S0, b0, S1, us, wb, hsto0, hown, hpf0, hseg, hat, hS, hwu0, hus, hn, hlo, hhi, htw, hwb, hfa,
    hlow, hR⟩ := h
  have hwb' : wb < c.mem.size := hwb
  have hpre : ∀ t, t < c.mem.size → (c.mem.push ⟨a, v, w⟩)[t]? = c.mem[t]? := TermInterf.push_pre
  have hwin : winL wb (th.promises ++ [c.mem.size]) = winL wb th.promises := by
    unfold winL
    rw [List.filter_append]
    have : List.filter (fun t => decide (t ≤ wb)) [c.mem.size] = [] := by
      simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, Nat.not_le.2 hwb', ↓reduceIte]
    rw [this, List.append_nil]
  refine ⟨c1, sb, S0, b0, S1, us, wb, hsto0, hown, hpf0, hseg, hat, hS, hwu0, hus, hn, hlo, hhi, htw,
    (show wb < (c.mem.push ⟨a, v, w⟩).size by rw [Array.size_push]; exact Nat.lt_succ_of_lt hwb'),
    fun tf mf h1 h2 h3 => ?_, fun t' m' h1 h2 h3 h4 h5 h6 => ?_, ?_⟩
  · by_cases hts : tf < c.mem.size
    · have h2' : (c.mem.push ⟨a, v, w⟩)[tf]? = some mf := h2
      rw [hpre tf hts] at h2'
      exact hfa tf mf h1 h2' h3
    · exact Nat.lt_of_lt_of_le hwb' (Nat.le_of_not_lt hts)
  · have h1' : t' ∈ th.promises ++ [c.mem.size] := h1
    rcases List.mem_append.1 h1' with h1 | h1
    · have h2' : (c.mem.push ⟨a, v, w⟩)[t']? = some m' := h2
      rw [hpre t' (hPlt t' h1)] at h2'
      exact hlow t' m' h1 h2' h3 h4 h5 h6
    · rw [List.mem_singleton] at h1; subst h1
      exact absurd (Nat.lt_of_le_of_lt h6 hwb') (Nat.lt_irrefl _)
  · rcases hR with ⟨K, ws, R0, hl, hv, hle, hp⟩ | e
    · refine Or.inl ⟨K, ws, R0, hl, hv, hle, fun i o w0 t' hK hI hw hL => ?_⟩
      have hL' : LowestIn (c.mem.push ⟨a, v, w⟩) (winL wb (th.promises ++ [c.mem.size])) _ t' := hL
      rw [hwin] at hL'
      have hW : ∀ t, t ∈ winL wb th.promises → t < c.mem.size :=
        fun t ht => hPlt t (TermPlant.mem_winL.1 ht).1
      have hL0 := TermPlant.LowestIn_back hW hpre hL'
      exact TermPlant.PredAt_mono (hW t' hL0.1) hpre (hp i o w0 t' hK hI hw hL0)
    · exact Or.inr e

/-- (dedup) master of `ThSysAt_prom`: also exports `KeepNW` (old non-word credits kept). -/
theorem ThSysAt_promK {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) :
    ∃ S HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size) Eg (Tot j) HP' HS' cr' db' S ∧
      MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th) ∧
      MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j) ∧
      KeepNW (Cut Eg j S) c.mem th.promises (cr j) cr' ∧
      ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S := by
  obtain ⟨S, hS0⟩ := X.inv.thr j th X.hth
  obtain ⟨hRE, hTE, hm, hHP, hHS, hC⟩ := id hS0
  have hH := MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hHP hHS
  obtain ⟨H', cr'', db', hag, hRE', hm', hH', hC'', heq⟩ :=
    tstepMC_promEc hRE hm hH (PromCrP_drop hC.toP) (hwu S) (hfw S)
  have hK := TermPlant.PromCrK_prom hC (fun t ht => X.inv.plt j th t X.hth ht) hag hC'' (promSelfK_any X)
  obtain ⟨HP', HS', hHs, hP', hS'⟩ := MemHeld_split (fun _ _ hc hp => Cut_cov hc hp) hH'
  refine ⟨S, HP', HS', fun t => if t < (stOf c.mem c.pairs th).mem.size then cr j t else cr'' t, db', ?_,
    ⟨hRE', hTE, hm', hP', hS', hK.1⟩, hm, hHP,
    fun t m ht _ _ => (by
      show (if t < c.mem.size then cr j t else _) = cr j t
      simp only [X.inv.plt j th t X.hth ht, ite_true]), hS0⟩
  show _ = _
  rw [← hHs]
  refine Res.ext fun key => ?_
  have e1 := congrArg (fun R : Res => R key) heq
  have e2 := congrArg (fun R : Res => R key) hK.2
  simp only [Res.add_apply] at e1 e2 ⊢
  omega

/-- (E1) **The promiser's `ThSysAt` after its promise, at the unplanted `Eg`**, with the
promise's accounting (`PAcct`).  The non-plant branch of `sysInv_prom` without its final
rewrite to `EgP`. -/
theorem ThSysAt_prom {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) :
    ∃ S HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size) Eg (Tot j) HP' HS' cr' db' S ∧
      MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th) ∧
      MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j) ∧
      ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S := by
    obtain ⟨x0, x1, x2, x3, x4, h0, h1, h2, h3, -, h4⟩ := ThSysAt_promK X hwu hfw
    exact ⟨x0, x1, x2, x3, x4, h0, h1, h2, h3, h4⟩

/-! ## (E2) The per-label plant hypotheses from the promise context -/

/-- (E2, **IniCap** derived) a private buffer's initialised count is at most its slot count:
`MemHeldP`'s entry is a `BufOKR` (an array has no word count). -/
theorem iniCap_of_heldP {E : TEnv} {s : St} {H : Res} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty}
    (h : MemHeldP E s H) (hp : Priv E l) (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) :
    E.ini l ≤ N := by
  obtain ⟨L, Rl, -, hcov, -, -, hent⟩ := h
  obtain ⟨vals, -, hok⟩ := (hent l (hcov l c hp hc)).2 c hc
  rcases hok with ⟨hw, -⟩ | ⟨N', e', us, Rs, hT', -, hn, -⟩
  · rw [hT] at hw; cases hw
  · rw [hT] at hT'; cases hT'; exact hn

theorem plantOf_some {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel} {f : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (h : TermPlantF.plantOf c Eg j a v w l = some f) :
    TermPlantF.PlantL c Eg j th a v w l ∧ f = plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := by
  unfold TermPlantF.plantOf at h
  rw [X.hth] at h
  by_cases hp : TermPlantF.PlantL c Eg j th a v w l
  · simp only [hp, ↓reduceIte, Option.some.injEq] at h
    exact ⟨hp, h.symm⟩
  · simp only [hp, ↓reduceIte] at h; cases h

theorem plantN_eq {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} (l : AllocLabel)
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) :
    TermPlantF.plantN c Eg j a v w l = NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := by
  unfold TermPlantF.plantN
  rw [X.hth]

theorem EgP_ini_some {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat} {l : AllocLabel}
    {f : Ts} (h : P l = some f) : (EgP Eg P N j n).ini l = max (Eg.ini l) (N l) := by
  simp [EgP, GEnv.withFp, plantG, h]

theorem EgP_pfr_some {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat} {l : AllocLabel}
    {f : Ts} (h : P l = some f) : (EgP Eg P N j n).pfr l = some f := by
  simp [EgP, GEnv.withFp, plantG, h]

/-- (E2) The promiser's promises at a planted label after its promise are typed words at the
published planted environment (`plantPromOK` for the old ones, `promNewOK` for the new one). -/
theorem promTyL {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel} {f : Ts} {cl : Cell}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hpl : TermPlantF.plantOf c Eg j a v w l = some f) (hcl : Eg.sto l = some cl) :
    ∀ t m, t ∈ (thP th c.mem.size).promises → (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc.label = l →
      WordOK (PubE (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size))
        cl.ty m.loc.offset (mw m) := by
  intro t m ht hm hl
  rcases List.mem_append.1 ht with ht | ht
  · have htl := X.inv.plt j th t X.hth ht
    rw [getElem_push_lt htl] at hm
    exact (hPO X l f hpl t m ht hm hl cl hcl).2
  · rw [List.mem_singleton] at ht; subst ht
    have e : m = ⟨a, v, w⟩ := by simpa using hm.symm
    subst e
    have hal : a.label = l := hl
    have hcl' : Eg.sto a.label = some cl := by rw [hal]; exact hcl
    exact (hNO X cl hcl' ⟨f, EgP_pfr_some (by rw [hal]; exact hpl)⟩).2

theorem AtOff_wordbuf {N n o : Nat} {P : Proto} (hP : P.ghost = false) (ho : o < N) :
    AtOff (.array (.lit N) (.word (.lit n) P)) o (.word (.lit n) P) := by
  have h := AtOff.elem (n := N) (j := o) (o := 0) (accs_word (r := .lit n) hP) ho
    (AtOff.here (Or.inl (by rw [accs_word hP]; exact Option.some_ne_none _)))
  have e : o * nWords [Acc.one] + 0 = o := by simp [nWords, Acc.size]
  rw [e] at h
  exact h

theorem Cut_plant1_ini {Eg : GEnv} {l : AllocLabel} {F : Ts} {Np i : Nat} {S : AllocLabel → Prop} :
    (Cut (plant1 Eg l F Np) i S).ini l = Np := plant1_ini_self Eg l F Np

theorem lt_of_max_ge {i k j : Nat} (h1 : i ≤ j) (h2 : j < max i k) : j < k := by
  rcases Nat.le_total i k with h | h
  · rw [Nat.max_eq_right h] at h2; exact h2
  · rw [Nat.max_eq_left h] at h2; exact absurd h1 (Nat.not_le.2 h2)

/-- (dedup) master of `plantStep`: also exports `KeepNW` (old non-word credits kept). -/
theorem plantStepK (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop} {l : AllocLabel} {f : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hm0 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th))
    (hH0 : MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j))
    (hpl : TermPlantF.plantOf c Eg j a v w l = some f)
    (hWB : ∀ cl, Eg.sto l = some cl → ∃ N n P, cl.ty = .array (.lit N) (.word (.lit n) P) ∧ P.ghost = false)
    (hR1w : ∀ i, Eg.ini l ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {Eg' : GEnv} {HP1 HS1 : Res} {cr1 db1 : Ts → Res}, PAgree Eg Eg' j l →
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size) Eg' (Tot j) HP1 HS1 cr1 db1 S →
      ∃ HP' HS' cr' db', ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (plant1 Eg' l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
          (max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))) (Tot j) HP' HS' cr' db' S ∧
        (HP' + HS') + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr' +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db1 =
          (HP1 + HS1) + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr1 +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db' ∧
        KeepNW (Cut Eg j S) (c.mem.push ⟨a, v, w⟩) (thP th c.mem.size).promises cr1 cr' := by
  intro Eg' HP1 HS1 cr1 db1 A h
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hpl
  obtain ⟨cl, hcl, ho, hnone, -, hcpl, hcT, hnT, hrT⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  obtain ⟨N, n, P, hTc, hPg⟩ := hWB cl hcl
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hb : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  -- the cut and its facts at `l`
  have hEsto : (Cut Eg j S).sto l = some cl := cutSto_own hcl ho
  have hPsto : (TermPlantF.cutP Eg j).sto l = some cl := cutSto_own hcl ho
  have hpriv : Priv (Cut Eg j S) l := ⟨⟨cl, hEsto, ho⟩, hnone⟩
  have hcap : Eg.ini l ≤ N := iniCap_of_heldP hH0 hpriv hEsto hTc
  have hkN : NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ≤ N := NpZ_le hPsto hTc
  rw [plantN_eq l X] at hR1w ⊢
  -- `PromAbove` after and before the promise
  have hpa1 : PromAbove (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := by
    have h1 := TermTyped.certified_promAboveSt X.cert hpi.2.1
    rw [hpi.2.2] at h1
    exact h1
  have hpa0 : PromAbove (stOf c.mem c.pairs th) := fun t ht m hm =>
    hpa1 t (List.mem_append_left _ ht) m (by
      show (c.mem.push ⟨a, v, w⟩)[t]? = some m
      rw [getElem_push_lt (hb t ht)]; exact hm)
  -- the frontier facts (`plant_holdF` before the promise)
  have hk : PrefixHeld (Cut Eg j S) (stOf c.mem c.pairs th) l cl
      (NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l) := PrefixHeld_NpZ hPsto
  obtain ⟨-, -, h3, h4⟩ := plant_holdF (E := Cut Eg j S)
    (E' := Cut (plant1 Eg l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
      (max (Eg.ini l) (NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l))) j S)
    hm0 hEsto ho hnone hpa0
    (fun Na e us hT _ => by
      rw [hTc] at hT; cases hT
      rw [Cut_plant1_ini]; exact Nat.max_le.2 ⟨hcap, hkN⟩)
    (held_of_prefix hk Cut_plant1_ini)
  have hFE : plantF (Cut Eg j S) (stOf c.mem c.pairs th) l =
      plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := plantF_congrE fun _ _ => Iff.rfl
  rw [hFE] at h3 h4
  -- the typed promises at `l`
  have hty := promTyL X hPO hNO hpl hcl
  refine ThSysAt_plant1BK A h hpa1 hcl ho hnone hTc hPg (X.inv.rle l) (Nat.le_max_left _ _)
    (Nat.max_le.2 ⟨hcap, hkN⟩) (h3.imp id (HoldW_prom hb)) (fun _ => Nat.le_max_left _ _)
    (hhold_prom (Q := fun o => InitR _ cl l o ∧ ¬ InitR _ cl l o) (fun o hQ => h4 o hQ.1 hQ.2) |>
      fun H o h1 h2 => H o ⟨h1, h2⟩)
    (fun b S' us hs ha h1 h2 => ?_) hcpl hcT hnT hrT ?_ ?_ hR1w ?_
  · -- hinh, from `plantInh`
    have hSw : S' = .word (.lit n) P := by
      rcases hs with ⟨-, rfl, -⟩ | ⟨N', us', j', he, -, -, -⟩
      · rw [hTc] at ha; cases ha
      · rw [hTc] at he; cases he; rfl
    have hI : IniSeg (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        j S) cl l b := by
      refine (IniSeg_iff ?_).2 h1
      rw [Cut_plant1_ini]
      exact (EgP_ini_some (j := j) (n := c.mem.size) hpl).trans (by rw [plantN_eq l X])
    obtain ⟨ws, hv, hl⟩ := hInh X j S l f cl b S' us hpl hcl hs ha h2 hI
    subst hSw
    exact ⟨ws, ValOf_word hv, hl⟩
  · -- FlipOK at `l` after the promise
    intro _ t m ht hm hl hwu hiw
    have hok := hty t m ht hm hl
    rw [hTc] at hok
    obtain ⟨hp, v', hv, hin⟩ := WordOK_wordbuf hok hPg
    have hoff : m.loc.offset < Eg.ini l := by
      have h5 : m.loc.offset < Eg.ini m.loc.label * nWords [Acc.one] :=
        hiw cl N (.word (.lit n) P) [.one] (by rw [hl]; exact hEsto) hTc (accs_word hPg)
      rw [hl] at h5; simpa [nWords, Acc.size] using h5
    refine ⟨cl, n, P, hEsto, hTc ▸ AtOff_wordbuf hPg (Nat.lt_of_lt_of_le hoff hcap), hPg, ?_, hp, v', hv, hin⟩
    intro N' e' hT'
    rw [hTc] at hT'; cases hT'
    refine Or.inr ⟨[.one], m.loc.offset, 0, accs_word hPg, by rw [hl]; exact hoff, by simp [nWords, Acc.size],
      AtOff.here (Or.inl (by rw [accs_word hPg]; exact Option.some_ne_none _))⟩
  · -- FpOK after the promise
    have h0 := X.inv.fpok j th S X.hth
    refine ⟨fun t ht => ?_, fun t m ht hm => h0.2 t m ht ?_⟩
    · have := h0.1 t ht
      show t < (c.mem.push ⟨a, v, w⟩).size
      rw [Array.size_push]; exact Nat.lt_succ_of_lt this
    · have hm' : (c.mem.push ⟨a, v, w⟩)[t]? = some m := hm
      rw [getElem_push_lt (mem := c.mem) (h0.1 t ht)] at hm'; exact hm'
  · -- hval, from `hval_of`
    refine hval_of (E0 := PubE (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j
      c.mem.size)) hTc hPg (fun i h1 h2 => ?_) (fun i h1 h2 => ?_) hty
    · obtain ⟨t0, m0, a1, a2, a3, a4, -, a6⟩ := hR1w i h1 h2
      exact ⟨t0, m0, a1, a2, a3, a4, a6⟩
    · have hik := lt_of_max_ge h1 h2
      rcases hk N (.word (.lit n) P) [.one] hTc (accs_word hPg) i (by simpa [nWords, Acc.size] using hik) with
        hI | ⟨u, hu, m, hm, hml⟩
      · have := hI N (.word (.lit n) P) [.one] hTc (accs_word hPg)
        have e : (Cut Eg j S).ini l * nWords [Acc.one] = Eg.ini l := by simp [Cut, nWords, Acc.size]
        rw [e] at this
        exact absurd h1 (Nat.not_le.2 this)
      · exact ⟨u, m, List.mem_append_left _ hu, by rw [getElem_push_lt (hb u hu)]; exact hm, hml⟩

/-- (E2) **One planted label's step**: from the promise context, the plant of `l` at any partial
plant agreeing with `Eg` at `l` (`ThSysAt_plant1B` with every hypothesis derived, except the
residual `hR1w` = PrivSlotFresh and the word-buffer shape `hWB`). -/
theorem plantStep (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop} {l : AllocLabel} {f : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hm0 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th))
    (hH0 : MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j))
    (hpl : TermPlantF.plantOf c Eg j a v w l = some f)
    (hWB : ∀ cl, Eg.sto l = some cl → ∃ N n P, cl.ty = .array (.lit N) (.word (.lit n) P) ∧ P.ghost = false)
    (hR1w : ∀ i, Eg.ini l ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {Eg' : GEnv} {HP1 HS1 : Res} {cr1 db1 : Ts → Res}, PAgree Eg Eg' j l →
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size) Eg' (Tot j) HP1 HS1 cr1 db1 S →
      ∃ HP' HS' cr' db', ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (plant1 Eg' l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
          (max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))) (Tot j) HP' HS' cr' db' S ∧
        (HP' + HS') + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr' +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db1 =
          (HP1 + HS1) + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr1 +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db' :=
  fun A h => by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := plantStepK (hV0 := hV0) hP hrun X hPO hNO hInh hm0 hH0 hpl hWB hR1w hPS hSub hSig A h
    exact ⟨x0, x1, x2, x3, h0, h1⟩

/-! ## (E5, A′) A planted label with no new slots: the flip alone -/

/-- (E5) `FlipOK` after the promise at any label, from the tied certificate (`flipOK_cert`). -/
theorem flipOK_post (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S)
    (hTE : ThInvE p (Cut Eg j S) (thP th c.mem.size))
    (hm : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)))
    (l : AllocLabel) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : FlipOK (Cut Eg j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) l := by
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  obtain ⟨ρe, ηe, cxe, hEe0, -⟩ := id hTE
  have hT' : ThInvE p (CE ηe) (thP th c.mem.size) := by rw [hEe0]; exact hTE
  have hm' : MemInv (gOf p k arch (promise c j a v w) j) (CE ηe)
      (stOf (promise c j a v w).mem (promise c j a v w).pairs (thP th c.mem.size)) := by
    rw [TermTyped.gOf_promise, hEe0, hpi.1]; exact hm
  have hSC : TermTyped.StoClo (CE ηe) := by
    rw [hEe0]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hbo : (gOf p k arch (promise c j a v w) j).boxFence = true := by
    rw [TermTyped.gOf_promise]; exact X.inv.bf
  have h := TermTyped.flipOK_cert (η := ηe) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (fun c1 h1 h2 => (hrun X S hS c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc')
    (fun c1 h1 h2 => by rw [hEe0]; exact (hrun X S hS c1 h1 h2).2)
    hpi.2.1 hT' hm' X.cert hSC hbo (l := l)
    (hrc := by
      rw [hEe0]; show TermTyped.RiniCoh _ (stOf (promise c j a v w).mem (promise c j a v w).pairs
        { th with promises := th.promises ++ [c.mem.size] })
      rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (hfl := fun l cl f hs hp => by
      rw [hEe0] at hs hp
      exact Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
        (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
    (hTA := by rw [hEe0]; exact TermMain.tidAt_cutP X.inv j S)
    (hTy := by rw [hEe0, TermTyped.gOf_promise]; exact (X.inv.tyRec X.hth S).1)
    (hRc := by rw [TermTyped.gOf_promise]; exact (X.inv.tyRec X.hth S).2)
  rw [hEe0, hpi.1] at h
  exact h

/-- (dedup) master of `flipStep`: also exports `KeepNW` (old non-word credits kept). -/
theorem flipStepK (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop} {l : AllocLabel} {f : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S)
    (hm0 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th))
    (hH0 : MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j))
    (hTE1 : ThInvE p (Cut Eg j S) (thP th c.mem.size))
    (hm1 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)))
    (hpl : TermPlantF.plantOf c Eg j a v w l = some f)
    (hno : TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {Eg' : GEnv} {HP1 HS1 : Res} {cr1 db1 : Ts → Res}, PAgree Eg Eg' j l →
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size) Eg' (Tot j) HP1 HS1 cr1 db1 S →
      ∃ HP' HS' cr' db', ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (plant1 Eg' l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
          (max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))) (Tot j) HP' HS' cr' db' S ∧
        (HP' + HS') + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr' +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db1 =
          (HP1 + HS1) + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr1 +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db' ∧
        KeepNW (Cut Eg j S) (c.mem.push ⟨a, v, w⟩) (thP th c.mem.size).promises cr1 cr' := by
  intro Eg' HP1 HS1 cr1 db1 A h
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hpl
  obtain ⟨cl, hcl, ho, hnone, -, hcpl, hcT, hnT, hrT⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hb : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  have hEsto : (Cut Eg j S).sto l = some cl := cutSto_own hcl ho
  have hPsto : (TermPlantF.cutP Eg j).sto l = some cl := cutSto_own hcl ho
  have hpriv : Priv (Cut Eg j S) l := ⟨⟨cl, hEsto, ho⟩, hnone⟩
  rw [plantN_eq l X] at hno ⊢
  have hpa1 : PromAbove (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := by
    have h1 := TermTyped.certified_promAboveSt X.cert hpi.2.1
    rw [hpi.2.2] at h1
    exact h1
  have hpa0 : PromAbove (stOf c.mem c.pairs th) := fun t ht m hm =>
    hpa1 t (List.mem_append_left _ ht) m (by
      show (c.mem.push ⟨a, v, w⟩)[t]? = some m
      rw [getElem_push_lt (hb t ht)]; exact hm)
  have hk : PrefixHeld (Cut Eg j S) (stOf c.mem c.pairs th) l cl
      (NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l) := PrefixHeld_NpZ hPsto
  obtain ⟨-, -, h3, -⟩ := plant_holdF (E := Cut Eg j S)
    (E' := Cut (plant1 Eg l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
      (max (Eg.ini l) (NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l))) j S)
    hm0 hEsto ho hnone hpa0
    (fun Na e us hT _ => by
      rw [Cut_plant1_ini, Nat.max_eq_left hno]; exact iniCap_of_heldP hH0 hpriv hEsto hT)
    (held_of_prefix hk Cut_plant1_ini)
  have hFE : plantF (Cut Eg j S) (stOf c.mem c.pairs th) l =
      plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := plantF_congrE fun _ _ => Iff.rfl
  rw [hFE] at h3
  have h0 := X.inv.fpok j th S X.hth
  refine ThSysAt_flip1BK A h hpa1 hcl ho hnone (X.inv.rle l) (Nat.max_eq_left hno)
    (h3.imp id (HoldW_prom hb)) hcpl hcT hnT hrT (flipOK_post (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hS hTE1 hm1 l) ⟨fun t ht => ?_, fun t m ht hm => h0.2 t m ht ?_⟩
  · have := h0.1 t ht
    show t < (c.mem.push ⟨a, v, w⟩).size
    rw [Array.size_push]; exact Nat.lt_succ_of_lt this
  · have hm' : (c.mem.push ⟨a, v, w⟩)[t]? = some m := hm
    rw [getElem_push_lt (mem := c.mem) (h0.1 t ht)] at hm'; exact hm'

/-- (E5, A′) **One planted label with no new slots** (`plantN ≤ ini`): its flip at any partial
plant agreeing with `Eg` at `l`, for any cell type, every hypothesis derived. -/
theorem flipStep (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop} {l : AllocLabel} {f : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S)
    (hm0 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf c.mem c.pairs th))
    (hH0 : MemHeldP (Cut Eg j S) (stOf c.mem c.pairs th) (HP j))
    (hTE1 : ThInvE p (Cut Eg j S) (thP th c.mem.size))
    (hm1 : MemInv (gOf p k arch c j) (Cut Eg j S) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)))
    (hpl : TermPlantF.plantOf c Eg j a v w l = some f)
    (hno : TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {Eg' : GEnv} {HP1 HS1 : Res} {cr1 db1 : Ts → Res}, PAgree Eg Eg' j l →
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size) Eg' (Tot j) HP1 HS1 cr1 db1 S →
      ∃ HP' HS' cr' db', ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (plant1 Eg' l (plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
          (max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l))) (Tot j) HP' HS' cr' db' S ∧
        (HP' + HS') + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr' +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db1 =
          (HP1 + HS1) + pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) cr1 +
            pSum (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) db' :=
  fun A h => by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := flipStepK (hV0 := hV0) hP hrun X hS hm0 hH0 hTE1 hm1 hpl hno hPS hSub hSig A h
    exact ⟨x0, x1, x2, x3, h0, h1⟩

/-! ## (E3) `ThSys_plantW` -/

/-- A duplicate-free list of the members of `L0` satisfying `Q`. -/
theorem exists_nodup_filter {α : Type} (Q : α → Prop) :
    ∀ L0 : List α, ∃ L : List α, L.Nodup ∧ ∀ x, x ∈ L ↔ x ∈ L0 ∧ Q x
  | [] => ⟨[], List.nodup_nil, fun x => by simp⟩
  | y :: L0 => by
    obtain ⟨L, hnd, hL⟩ := exists_nodup_filter Q L0
    by_cases hy : Q y ∧ y ∉ L
    · refine ⟨y :: L, List.nodup_cons.2 ⟨hy.2, hnd⟩, fun x => ?_⟩
      constructor
      · intro hx
        rcases List.mem_cons.1 hx with e | hx
        · subst e; exact ⟨List.mem_cons_self, hy.1⟩
        · exact ⟨List.mem_cons_of_mem _ ((hL x).1 hx).1, ((hL x).1 hx).2⟩
      · rintro ⟨hx, hq⟩
        rcases List.mem_cons.1 hx with e | hx
        · subst e; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((hL x).2 ⟨hx, hq⟩)
    · refine ⟨L, hnd, fun x => ⟨fun hx => ⟨List.mem_cons_of_mem _ ((hL x).1 hx).1, ((hL x).1 hx).2⟩, ?_⟩⟩
      rintro ⟨hx, hq⟩
      rcases List.mem_cons.1 hx with e | hx
      · subst e
        apply Classical.byContradiction; intro hn
        exact hy ⟨hq, hn⟩
      · exact (hL x).2 ⟨hx, hq⟩

/-- The label a message's location value points into. -/
def locLab (o : Option Msg) : Option AllocLabel :=
  o.bind fun m => match m.val with
    | .loc a' _ => some a'.label
    | _ => none

/-- (E3) **`ThSys_plantW`**: the promiser's part of a planting promise step (the `selfPlant`
field) for events whose planted labels are single-word protocol buffers, modulo the residual
PrivSlotFresh (`hR1w`) and the obligations `hwu`, `hfw`, `plantPromOK`, `promNewOK`, `plantInh`. -/
theorem ThSys_plantW (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S))
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hWB : ∀ l f cl, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → Eg.sto l = some cl →
      ∃ N n P, cl.ty = .array (.lit N) (.word (.lit n) P) ∧ P.ghost = false)
    (hR1w : ∀ l f, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → ∀ i, Eg.ini l ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' := by
  obtain ⟨S, HP1, HS1, cr1, db1, hacct, hT, hm0, hH0, hS0⟩ := ThSysAt_prom X hwu hfw
  -- the planted labels, as a duplicate-free list
  obtain ⟨Ls, hnd, hLs⟩ := exists_nodup_filter (fun l => TermPlantF.plantOf c Eg j a v w l ≠ none)
    ((th.promises ++ [c.mem.size]).filterMap fun t => locLab (c.mem.push ⟨a, v, w⟩)[t]?)
  have hmem : ∀ l, l ∈ Ls ↔ TermPlantF.plantOf c Eg j a v w l ≠ none := fun l => by
    refine ⟨fun h => ((hLs l).1 h).2, fun h => (hLs l).2 ⟨?_, h⟩⟩
    obtain ⟨f, hf⟩ : ∃ f, TermPlantF.plantOf c Eg j a v w l = some f := by
      cases e : TermPlantF.plantOf c Eg j a v w l with
      | none => exact absurd e h
      | some f => exact ⟨f, rfl⟩
    obtain ⟨⟨l', -, t, ht, m, hm, -, -, a', g, hv, hal, -⟩, -⟩ := plantOf_some X hf
    refine List.mem_filterMap.2 ⟨t, ht, ?_⟩
    simp only [locLab, hm, Option.bind_some, hv, hal]
  have hsome : ∀ l, l ∈ Ls → ∃ f, TermPlantF.plantOf c Eg j a v w l = some f := fun l hl => by
    have h := (hmem l).1 hl
    cases e : TermPlantF.plantOf c Eg j a v w l with
    | none => exact absurd e h
    | some f => exact ⟨f, rfl⟩
  have hown : ∀ l ∈ Ls, ∃ cl, Eg.sto l = some cl ∧ cl.owner = some (gOf p k arch c j).i := fun l hl => by
    obtain ⟨f, hf⟩ := hsome l hl
    obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hf
    obtain ⟨cl, hcl, ho, -⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
    exact ⟨cl, hcl, ho⟩
  obtain ⟨HP', HS', cr', db', hT', e2⟩ := ThSysAt_plantL
    (Fm := fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
    (Nm := fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) hnd hown
    (fun l hl => by
      obtain ⟨f, hf⟩ := hsome l hl
      by_cases hno : TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l
      · exact flipStep (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hS0 hm0 hH0 hT.2.1 hT.2.2.1 hf hno
      · exact plantStep (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hPO hNO hInh hm0 hH0 hf (fun cl => hWB l f cl hf hno) (hR1w l f hf hno)) hT
  have hG : plantL Eg (fun l => plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l)
      (fun l => max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l)) Ls =
      plantG Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) :=
    plantL_eq_plantG hmem (fun l f hf => ((plantOf_some X hf).2).symm) (fun _ _ => rfl)
  have hcut : Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      (gOf p k arch c j).i S = Cut (plantG Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w))
        (gOf p k arch c j).i S :=
    TermStepper.Cut_withFp _ _ _ _ (by show TermStepper.fpProm Eg j c.mem.size j = Eg.fpOf j; simp [TermStepper.fpProm])
  rw [hG] at hT'
  refine ⟨HP', HS', cr', db', acct_trans hacct e2, S, ?_⟩
  rw [hcut]
  exact hT'

/-! ## (E4) The `selfPlant` field from `ThSys_plantW` and two residual fields -/

/-- A single-word protocol buffer type. -/
def WordBufT (T : Ty) : Prop := ∃ N n P, T = .array (.lit N) (.word (.lit n) P) ∧ P.ghost = false

/-- (residual, **PrivSlotFresh**) every new unit of a planted word buffer has one placeholder
below and, otherwise, only the promiser's promises (`hR1w`). -/
def PrivSlotF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ l f, TermPlantF.plantOf c Eg j a v w l = some f → (∀ cl, Eg.sto l = some cl → WordBufT cl.ty) →
      ∀ i, Eg.ini l ≤ i → i < max (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) →
      ∃ t0 m0, (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 ∧ m0.loc = ⟨l, i⟩ ∧
      m0.val = .undef ∧ t0 ∉ (thP th c.mem.size).promises ∧ (∃ t, AtA (c.mem.push ⟨a, v, w⟩) ⟨l, i⟩ t0 t = true) ∧
      ∀ t m, (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, i⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧
        t ∈ (thP th c.mem.size).promises

/-- (residual, **selfPlantRest**) `selfPlant` at events planting a label with new slots
(`plantN > ini`) that is not a single-word protocol buffer. -/
def SelfPlantRestF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∃ l f cl, TermPlantF.plantOf c Eg j a v w l = some f ∧ ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l ∧
      Eg.sto l = some cl ∧ ¬ WordBufT cl.ty) →
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db'

/-- (E4) **`selfPlant`** from `ThSys_plantW` (word-buffer events) and `selfPlantRest` (the others). -/
theorem selfPlant_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hPS : PrivSlotF p k arch Sp Init MintOK c0) (hRest : SelfPlantRestF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) (hPSk : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' := by
  by_cases hW : ∀ l f cl, TermPlantF.plantOf c Eg j a v w l = some f →
      ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l → Eg.sto l = some cl → WordBufT cl.ty
  · exact ThSys_plantW (hV0 := hV0) (hPS := hPSk) (hSub := hSub) (hSig := hSig) hP hrun X hwu hfw hPO hNO hInh hW
      (fun l f hf hno => hPS X l f hf (fun cl hcl => hW l f cl hf hno hcl))
  · apply hRest X
    apply Classical.byContradiction; intro hn
    exact hW fun l f cl hf hno hcl => Classical.byContradiction fun hb => hn ⟨l, f, cl, hf, hno, hcl, hb⟩

end

#print axioms ThSysAt_promK
#print axioms plantStepK
#print axioms flipStepK

end TermPlantE

#print axioms TermPlantE.promSelfK_any
#print axioms TermPlantE.ThSysAt_prom
#print axioms TermPlantE.iniCap_of_heldP
#print axioms TermPlantE.promTyL
#print axioms TermPlantE.plantStep
#print axioms TermPlantE.flipOK_post
#print axioms TermPlantE.flipStep
#print axioms TermPlantE.ThSys_plantW
#print axioms TermPlantE.selfPlant_of
