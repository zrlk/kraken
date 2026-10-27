import WeakCore.TermExtMid
import WeakCore.SpawnArmZ
/-!
# ExtArmZ — the EM0 step relation `Spawn ∨ Ext`: leaf arms, runs, `SpawnArmX` and the finals (E2)

* `ext_shape`, `spLeafArms_ext` — an extern step replaces one thread (promises, views, stack unchanged; the new
  binding's words are constants), so the five run-closed leaves (`ViewInv`, `RunScope`, `PromViewLt`, `PromPos`,
  `PromNodupI`) are kept; `SpLeafArms.or`, `spLeafArms_em0`.
* `stepsE_cap_eq`, `trace_mono`, `siteNoProm_ext`, `site_noPromE` — run facts over `StepsE`.
* `spawnArmX_em0` — `SpawnArmX` at `Spawn ∨ Ext` (spawn: `TermSpawnMid.sysInvN_spawnArm`; extern:
  `TermExtMid.sysInvN_extStep`).
* `machine_tokens_main_em0`, `token_unique_net_em0`, `token_unique_final_em0`, `reachable_typed_em0` — the SpawnFinalX
  finals at `Sp := Spawn … c0.cap ∨ Ext …`, from `InitOK`.
-/

namespace ExtArmZ
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn TermExtStep A9SpawnFinal TermCertScope TermTyped TermSpawnStep TermExtMid
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-! ## The extern step as a thread replacement (leaf arms) -/
section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem wake_all {c : Cfg} {i : Nat} {v : Ts} {n : ExtName} {ws : List Word} {Q : TTh → Prop}
    (hQ : ∀ th u, Q th → Q { th with permit := some u }) (h : ∀ (j : Nat) (t : TTh), c.ths[j]? = some t → Q t) :
    ∀ (j : Nat) (t : TTh), (wake c i v n ws).ths[j]? = some t → Q t := by
  intro j t hj
  rcases wake_get c i v n ws j with e | ⟨th, u, h1, h2⟩
  · rw [e] at hj; exact h j t hj
  · rw [h2] at hj; cases hj; exact hQ th u (h j th h1)

theorem viewInv_wake {c : Cfg} {i : Nat} {v : Ts} {n : ExtName} {ws : List Word} (hv : TermViewInv.ViewInv c) :
    TermViewInv.ViewInv (wake c i v n ws) := by
  refine ⟨by rw [wake_mem]; exact hv.1, ?_⟩
  rw [wake_mem]; exact wake_all (fun _ _ h => h) hv.2

theorem runScope_wake {c : Cfg} {i : Nat} {v : Ts} {n : ExtName} {ws : List Word} (hd : TermScope.RunScope c) :
    TermScope.RunScope (wake c i v n ws) :=
  wake_all (Q := TermScope.ThScope) (fun _ _ h => ⟨h.ok, h.σs, h.env, h.stk⟩) hd

theorem promViewLt_wake {c : Cfg} {i : Nat} {v : Ts} {n : ExtName} {ws : List Word} (hc : TermPlantF.PromViewLt c) :
    TermPlantF.PromViewLt (wake c i v n ws) := by
  intro j t q hj hq
  rw [wake_mem]
  exact wake_all (Q := fun t => ∀ q ∈ t.promises, ∃ m : Msg, c.mem[q]? = some m ∧ m.view < q) (fun _ _ h => h)
    (fun j t hj q hq => hc j t q hj hq) j t hj q hq

theorem promPos_wake {c : Cfg} {i : Nat} {v : Ts} {n : ExtName} {ws : List Word} (hc : TermPlantAtPos.PromPos c) :
    TermPlantAtPos.PromPos (wake c i v n ws) :=
  wake_all (Q := fun t => ∀ q ∈ t.promises, 0 < q) (fun _ _ h => h) hc

theorem promNodup_wake {c : Cfg} {i : Nat} {v : Ts} {n : ExtName} {ws : List Word} (hc : TermBal.PromNodupI c) :
    TermBal.PromNodupI (wake c i v n ws) := by
  have hp : ∀ j, TermFul.promsOf (wake c i v n ws) j = TermFul.promsOf c j := by
    intro j
    unfold TermFul.promsOf
    rcases wake_get c i v n ws j with e | ⟨th, u, h1, h2⟩
    · rw [e]
    · rw [h1, h2]; rfl
  refine ⟨?_, wake_all (Q := fun t => t.promises.Nodup) (fun _ _ h => h) hc.2⟩
  rcases hc.1 with h0 | hW
  · exact .inl (by rw [wake_size]; exact h0)
  · refine .inr fun j => ?_
    obtain ⟨h1, h2⟩ := hW j
    refine ⟨by rw [wake_pairs, wake_mem]; exact h1, fun t ht => ?_⟩
    rw [hp] at ht; rw [wake_mem, wake_pairs]; exact h2 t ht

theorem siteNoProm_wake {c : Cfg} {i : Nat} {v : Ts} {n : ExtName} {ws : List Word} (h0 : TermSpawnStep.SiteNoProm c) :
    TermSpawnStep.SiteNoProm (wake c i v n ws) :=
  wake_all (Q := fun t => TermSpawnStep.AtSite t → t.promises = []) (fun _ _ h hs => h hs) h0

/-- An extern step replaces thread `i` (certified there), then `unpark`'s wake sets at most one permit. -/
theorem ext_shape {c c' : Cfg} (h : Ext p k arch c c') :
    ∃ (i : Nat) (th th' : TTh) (tr : List Event) (wn : ExtName) (wws : List Word) (wv : Ts), c.ths[i]? = some th ∧
      Certified p k arch (TermSetTh.setC c i th' tr) i ∧
      th'.promises = th.promises ∧ th'.vs = { th.vs with vRd := th'.vs.vRd, vPreBase := th'.vs.vPreBase } ∧
      (TermViewInv.VSB c.mem.size th.vs → TermViewInv.VSB c.mem.size th'.vs) ∧ th'.stack = th.stack ∧ th'.σs = th.σs ∧
      (∃ (x : String) (n : ExtName) (a : At) (e : Expr) (ws : List Word), th.term = .let_ x (.ext n a) e ∧
        th'.term = e ∧ th'.env = (x, n.sig.2, ws) :: th.env ∧ (∀ w ∈ ws, w.view = 0 ∧ w.rts = 0) ∧
        (ExtNeedsNoProm n th → th.promises = [])) ∧
      c' = wake (TermSetTh.setC c i th' tr) i wv wn wws := by
  obtain ⟨i, x, n, a, e, th, rt, ws, rs, hth, hterm, hnp, -, hadm, hcert, rfl⟩ := h.elim
  have hrs := (mem_resultsL n i ws c.trace rs).2 hadm
  by_cases hc : n = .current
  · subst hc
    have hw : ∀ c0 : Cfg, wake c0 i (relView th.vs) .current ws = c0 :=
      fun c0 => wake_of_ne c0 i _ ws (by intro h; cases h)
    have hx : extCfg c i th x .current e ws rs = curCfg c i th x e := rfl
    rw [hx] at hcert
    rw [hw, hx]
    cases htl : th.tidLbl with
    | some l =>
      refine ⟨i, th, { th with term := e, env := (x, ExtName.current.sig.2, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env },
        c.trace, .current, ws, relView th.vs, hth, by rw [← curCfg_some htl]; exact hcert, rfl, rfl, id, rfl, rfl,
        ⟨x, .current, a, e, [cst (.loc ⟨l, 0⟩ 0)], hterm, rfl, rfl, by simp [cst, Promises.TVal.mk0], hnp⟩, ?_⟩
      rw [hw]; exact curCfg_some htl
    | none =>
      have hcc : curCfg c i th x e = TermSetTh.setC c i
          { th with nalloc := th.nalloc + 1, tidLbl := some (freshLabel c.lbase c.n i th.nalloc), term := e,
                    env := (x, .tid, [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env } c.trace := by
        unfold curCfg; rw [htl]; rfl
      refine ⟨i, th,
        { th with nalloc := th.nalloc + 1, tidLbl := some (freshLabel c.lbase c.n i th.nalloc), term := e,
                  env := (x, .tid, [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env },
        c.trace, .current, ws, relView th.vs, hth, by rw [← hcc]; exact hcert, rfl, rfl, id, rfl, rfl,
        ⟨x, .current, a, e, [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)], hterm, rfl, rfl,
          by simp [cst, Promises.TVal.mk0], hnp⟩, ?_⟩
      rw [hw]; exact hcc
  · have hcfg : extCfg c i th x n e ws rs = TermSetTh.setC c i
        { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := if n = .park then parkVs c.mem.size th else th.vs,
                  permit := if n = .park then none else th.permit }
        (c.trace ++ n.events ws rs) := by
      cases n <;> first | exact absurd rfl hc | rfl
    have hvs : (if n = .park then parkVs c.mem.size th else th.vs) =
        { th.vs with vRd := (if n = .park then parkVs c.mem.size th else th.vs).vRd,
                     vPreBase := (if n = .park then parkVs c.mem.size th else th.vs).vPreBase } := by
      split
      · unfold parkVs; split <;> rfl
      · rfl
    rw [hcfg] at hcert ⊢
    generalize hT : ({ th with term := e, env := (x, n.sig.2, rs) :: th.env,
                               vs := (if n = .park then parkVs c.mem.size th else th.vs),
                               permit := (if n = .park then none else th.permit) } : TTh) = th1 at hcert ⊢
    generalize hR : c.trace ++ n.events ws rs = tr1 at hcert ⊢
    refine ⟨i, th, th1, tr1, n, ws, relView th.vs, hth, hcert, by rw [← hT], by rw [← hT]; exact hvs,
      fun h => by rw [← hT]; exact TermViewInv.parkVs_vsb_if n h, by rw [← hT], by rw [← hT],
      ⟨x, n, a, e, rs, hterm, by rw [← hT], by rw [← hT], ?_, hnp⟩, rfl⟩
    intro w hw
    obtain ⟨m, rfl⟩ := TermRun.resultsL_num hc hrs w hw
    simp [cst, Promises.TVal.mk0]

theorem viewInv_ext {c c' : Cfg} (h : Ext p k arch c c') (hv : TermViewInv.ViewInv c) : TermViewInv.ViewInv c' := by
  obtain ⟨i, th, th', tr, wn, wws, wv, hth, -, -, -, hvsb, hst, -, ⟨x, n, a, e, ws, -, -, henv, hws, -⟩, rfl⟩ :=
    ext_shape h
  refine viewInv_wake ?_
  refine ⟨hv.1, fun j t hj => ?_⟩
  rcases TermSetTh.setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
  · obtain ⟨h1, h2, h3⟩ := hv.2 _ th hth
    refine ⟨?_, by rw [hst]; exact h2, hvsb h3⟩
    rw [henv]
    intro en hen
    rcases List.mem_cons.1 hen with rfl | hen
    · intro w hw
      obtain ⟨e1, e2⟩ := hws w hw
      exact ⟨by rw [e1, e2]; exact Nat.le_refl _, by rw [e2]; exact Nat.zero_le _⟩
    · exact h1 en hen
  · exact hv.2 j t hj'

theorem runScope_ext {c c' : Cfg} (h : Ext p k arch c c') (hd : TermScope.RunScope c) : TermScope.RunScope c' := by
  obtain ⟨i, th, th', tr, wn, wws, wv, hth, -, -, -, -, hst, hσ, ⟨x, n, a, e, ws, hterm, hte, henv, -⟩, rfl⟩ :=
    ext_shape h
  refine runScope_wake ?_
  intro j t hj
  rcases TermSetTh.setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
  · obtain ⟨hok, hσs, he, hstk⟩ := hd _ th hth
    rw [hterm] at hok he
    simp only [TermScope.allOK, Bool.and_eq_true] at hok
    refine ⟨by rw [hte]; exact hok.2, by rw [hσ]; exact hσs, ?_, by rw [hst]; exact hstk⟩
    rw [hte, henv]
    exact TermScope.envDRF_cons (fun _ => by cases n <;> rfl)
      (fun y hy hne => he y (TermScope.free_let_body hy hne))
  · exact hd j t hj'

theorem promViewLt_ext {c c' : Cfg} (h : Ext p k arch c c') (hc : TermPlantF.PromViewLt c) :
    TermPlantF.PromViewLt c' := by
  obtain ⟨i, th, th', tr, wn, wws, wv, hth, -, hp, -, -, -, -, -, rfl⟩ := ext_shape h
  refine promViewLt_wake ?_
  intro j t q hj hq
  rcases TermSetTh.setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
  · rw [hp] at hq; exact hc _ th q hth hq
  · exact hc j t q hj' hq

theorem promPos_ext {c c' : Cfg} (h : Ext p k arch c c') (hc : TermPlantAtPos.PromPos c) :
    TermPlantAtPos.PromPos c' := by
  obtain ⟨i, th, th', tr, wn, wws, wv, hth, -, hp, -, -, -, -, -, rfl⟩ := ext_shape h
  refine promPos_wake ?_
  intro j t hj q hq
  rcases TermSetTh.setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
  · rw [hp] at hq; exact hc _ th hth q hq
  · exact hc j t hj' q hq

theorem promNodup_ext {c c' : Cfg} (h : Ext p k arch c c') (hc : TermBal.PromNodupI c) :
    TermBal.PromNodupI c' := by
  obtain ⟨i, th, th', tr, wn, wws, wv, hth, -, hp, -, -, -, -, -, rfl⟩ := ext_shape h
  refine promNodup_wake ?_
  refine ⟨?_, fun j t hj => ?_⟩
  · rcases hc.1 with h0 | hW
    · exact .inl (by rw [TermSetTh.setC_size]; exact h0)
    · refine .inr fun j => ?_
      have hpj := TermSetTh.setC_promises (tr := tr) hth hp j
      obtain ⟨h1, h2⟩ := hW j
      refine ⟨h1, fun t ht => ?_⟩
      have ht' : t ∈ TermFul.promsOf c j := by
        unfold TermFul.promsOf at ht ⊢; rw [hpj] at ht; exact ht
      exact h2 t ht'
  · rcases TermSetTh.setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
    · rw [hp]; exact hc.2 _ th hth
    · exact hc.2 j t hj'

theorem spLeafArms_ext : SpLeafArms (Ext p k arch) :=
  ⟨fun _ _ h => viewInv_ext h, fun _ _ h => runScope_ext h, fun _ _ h => promViewLt_ext h,
    fun _ _ h => promPos_ext h, fun _ _ h => promNodup_ext h⟩

/-- The leaf arms of a disjunction of steps. -/
theorem SpLeafArms.or {Sp1 Sp2 : Cfg → Cfg → Prop} (L1 : SpLeafArms Sp1) (L2 : SpLeafArms Sp2) :
    SpLeafArms (fun c c' => Sp1 c c' ∨ Sp2 c c') :=
  ⟨fun c c' h => h.elim (L1.viewInv c c') (L2.viewInv c c'), fun c c' h => h.elim (L1.runDRF c c') (L2.runDRF c c'),
    fun c c' h => h.elim (L1.promViewLt c c') (L2.promViewLt c c'),
    fun c c' h => h.elim (L1.promPos c c') (L2.promPos c c'),
    fun c c' h => h.elim (L1.promNodup c c') (L2.promNodup c c')⟩

theorem spLeafArms_em0 {cap : Nat} :
    SpLeafArms (fun c c' => TermSpawnStep.Spawn p k arch cap c c' ∨ Ext p k arch c c') :=
  SpLeafArms.or SpawnLeafZ.spLeafArms_spawn spLeafArms_ext

end

/-! ## Runs with spawns and extern steps -/
section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

/-- An `Ext` step keeps the capacity. -/
theorem Ext.cap_eq {c c' : Cfg} (h : Ext p k arch c c') : c'.cap = c.cap := (Ext.frame h).2.2.1

/-- **The capacity along a run** with spawns and extern steps. -/
theorem stepsE_cap_eq {cap : Nat} {c0 c : Cfg} (h : StepsE p k arch cap c0 c) : c.cap = c0.cap :=
  TermSpawnStep.stepsG_pres (P := fun c => c.cap = c0.cap)
    (fun _ _ hs e => (TermStep.step_cap hs).trans e)
    (fun _ _ hs e => hs.elim (fun h => (TermSpawnMid.Spawn.cap_eq h).trans e) (fun h => (Ext.cap_eq h).trans e)) h rfl

/-- No machine step changes the trace. -/
theorem step_trace {c c' : Cfg} (h : Step p k arch c c') : c'.trace = c.trace := by
  cases h with
  | thread i hs _ =>
      obtain ⟨_, _, _, _, _, _, rfl⟩ := step_thread_inv hs
      rfl
  | prom i a v w _ _ _ =>
      unfold promise; split <;> rfl

/-- No spawn changes the trace. -/
theorem spawn_trace {cap : Nat} {c c' : Cfg} (h : TermSpawnStep.Spawn p k arch cap c c') : c'.trace = c.trace := by
  obtain ⟨i, x, f, a, T, ts, e, th, rt, ws, -, -, -, -, -, rfl⟩ := TermSpawnStep.Spawn.elim h
  rfl

/-- **`trace_mono`**: along a run with spawns and extern steps the trace only grows (behaviours
read the delta `c.trace.drop c0.trace.length`). -/
theorem trace_mono {cap : Nat} {c0 c : Cfg} (h : StepsE p k arch cap c0 c) : c0.trace <+: c.trace :=
  TermSpawnStep.stepsG_pres (P := fun c => c0.trace <+: c.trace)
    (fun _ _ hs e => by rw [step_trace hs]; exact e)
    (fun _ _ hs e => hs.elim (fun h => by rw [spawn_trace h]; exact e)
      (fun h => e.trans (Ext.frame h).2.2.2.2.2)) h (List.prefix_refl _)

/-- An extern step keeps `SiteNoProm`: if the stepping thread lands at a spawn site, it is certified
there, so it has no promises (`cert_site`). -/
theorem siteNoProm_ext {c c' : Cfg} (h : Ext p k arch c c') (h0 : TermSpawnStep.SiteNoProm c) :
    TermSpawnStep.SiteNoProm c' := by
  obtain ⟨i, th, th', tr, wn, wws, wv, hth, hcert, -, -, -, -, -, -, rfl⟩ := ext_shape h
  refine siteNoProm_wake ?_
  intro j t hj hs
  rcases TermSetTh.setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
  · exact TermSpawnStep.cert_site hj hs hcert
  · exact h0 j t hj' hs

/-- **`site_noProm`** over runs with spawns and extern steps (`TermSpawnStep.site_noProm`, for `StepsX`). -/
theorem site_noPromE {cap : Nat} {c0 c : Cfg} (hr : StepsE p k arch cap c0 c) (h0 : TermSpawnStep.SiteNoProm c0)
    {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) {x f : String} {a : At} {T : Ty} {ts : List Ty} {e : Expr}
    (he : th.term = .let_ x (.spawn f a T ts) e) : th.promises = [] :=
  have h : TermSpawnStep.SiteNoProm c :=
    TermSpawnStep.stepsG_pres (P := TermSpawnStep.SiteNoProm) (fun _ _ h => TermSpawnStep.siteNoProm_step h)
      (fun _ _ h => h.elim (fun h => TermSpawnStep.siteNoProm_spawn h) (fun h => siteNoProm_ext h)) hr h0
  h i th hth ⟨x, f, a, T, ts, e, he⟩

end

/-! ## `SpawnArmX` at `Spawn ∨ Ext`, and the EM0 finals -/

/-- **The step arm at `Spawn ∨ Ext`** (the `SpawnArmX` split): a spawn by `TermSpawnMid.sysInvN_spawnArm` (capacity
from `stepsE_cap_eq`), an extern step by `sysInvN_extStep`.  No hypotheses. -/
theorem spawnArmX_em0 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg} :
    SpawnArmX p k arch (fun c c' => TermSpawnStep.Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init c0 := by
  intro _ _ _ c c' hr hI hsp
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs⟩ := hI
  rcases hsp with hs | hx
  · exact TermSpawnMid.sysInvN_spawnArm hN hOL hObs hs (stepsE_cap_eq hr)
  · exact sysInvN_extStep hN hOL hObs hx

/-- **`machine_tokens_mainX` at `Sp := Spawn ∨ Ext`, from `InitOK`** (all Sp-arms discharged). -/
theorem machine_tokens_main_em0 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsFX p k arch (fun c c' => TermSpawnStep.Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hk : k.storeDepRts = true) (h0 : InitOK p k arch Init (fun _ => True) c0)
    {c : Cfg} (hr : StepsE p k arch c0.cap c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  machine_tokens_mainX O hk (startOKX_of_initOK h0) spLeafArms_em0 spawnArmX_em0 hr

/-- **`token_unique_netX` at `Sp := Spawn ∨ Ext`, from `InitOK`**. -/
theorem token_unique_net_em0 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsFX p k arch (fun c c' => TermSpawnStep.Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hk : k.storeDepRts = true) (h0 : InitOK p k arch Init (fun _ => True) c0)
    {c : Cfg} (hr : StepsE p k arch c0.cap c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_netX O hk (startOKX_of_initOK h0) spLeafArms_em0 spawnArmX_em0 hr

/-- **`token_unique_finalX` at `Sp := Spawn ∨ Ext`, from `InitOK`**. -/
theorem token_unique_final_em0 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsFX p k arch (fun c c' => TermSpawnStep.Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hk : k.storeDepRts = true) (h0 : InitOK p k arch Init (fun _ => True) c0)
    {c : Cfg} (hr : StepsE p k arch c0.cap c0 c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_finalX O hk (startOKX_of_initOK h0) spLeafArms_em0 spawnArmX_em0 hr hn

/-- **`reachable_typedX` at `Sp := Spawn ∨ Ext`, from `InitOK`**. -/
theorem reachable_typed_em0 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsFX p k arch (fun c c' => TermSpawnStep.Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hk : k.storeDepRts = true) (h0 : InitOK p k arch Init (fun _ => True) c0)
    {c : Cfg} (hr : StepsE p k arch c0.cap c0 c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot :=
  reachable_typedX O hk (startOKX_of_initOK h0) spLeafArms_em0 spawnArmX_em0 hr

end ExtArmZ

#print axioms ExtArmZ.ext_shape
#print axioms ExtArmZ.viewInv_ext
#print axioms ExtArmZ.runScope_ext
#print axioms ExtArmZ.promViewLt_ext
#print axioms ExtArmZ.promPos_ext
#print axioms ExtArmZ.promNodup_ext
#print axioms ExtArmZ.spLeafArms_ext
#print axioms ExtArmZ.SpLeafArms.or
#print axioms ExtArmZ.spLeafArms_em0
#print axioms ExtArmZ.Ext.cap_eq
#print axioms ExtArmZ.stepsE_cap_eq
#print axioms ExtArmZ.step_trace
#print axioms ExtArmZ.spawn_trace
#print axioms ExtArmZ.trace_mono
#print axioms ExtArmZ.siteNoProm_ext
#print axioms ExtArmZ.site_noPromE
#print axioms ExtArmZ.spawnArmX_em0
#print axioms ExtArmZ.machine_tokens_main_em0
#print axioms ExtArmZ.token_unique_net_em0
#print axioms ExtArmZ.token_unique_final_em0
#print axioms ExtArmZ.reachable_typed_em0
