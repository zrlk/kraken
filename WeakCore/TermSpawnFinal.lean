import WeakCore.TermSpawnArg
/-!
# TermSpawnFinal — `startOK_spawnS`, proved

With the statement's pending extra hypotheses `hstk0`, `hstk`, `hR0a`.
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermSpawnSim

/-- Each kid's entry frame, from the setup thread's end at the phantom configuration. -/
theorem kid_both {p : Prog} {Eg Eg2 : GEnv} {S S2 : AllocLabel → Prop} {j : Nat} {th : TTh} {res : List Word}
    {kd : Kid} {R0 : Ty} {T0 : Res} {a : At} {rt : Ty}
    (hR : ThInvRE p (Cut Eg 0 S) (app (f0 R0) th) T0) (hS : SeenLE (Cut Eg 0 S) th.vs.vRelSt)
    (hstk : th.stack = []) (hret : th.term = .ret a) (hev : evalAt th.env a = some (rt, res))
    (hR0 : R0.wf 0 0 = true) (hI : InclS (Cut Eg 0 (fun _ => False)) (Cut Eg2 j S2)) (hp2 : Eg2.prog = Eg.prog)
    (hok : KidOK p R0 kd) (T : Res) :
    ThInvRE p (Cut Eg2 j S2) (kidTh th.vs res kd) T ∧ ThInvE p (Cut Eg2 j S2) (kidTh th.vs res kd) := by
  have hp : Eg.prog = p := by
    obtain ⟨_, η, _, _, _, hCE, hE, -⟩ := hR
    exact (congrArg TEnv.prog hCE).symm.trans hE.1
  have kv := kid_val (hp2.trans hp) hI hS (vr_of_ret hR hstk hret hev hR0) hok
  obtain ⟨-, -, -, -, hts, hwt, ⟨r, hchk, htv⟩, -⟩ := hok
  exact entryR_of T (hp2.trans hp) rfl rfl rfl rfl hchk htv kv.1 kv.2 hts hwt

theorem kid_lbl {p : Prog} {Eg : GEnv} {S : AllocLabel → Prop} {th : TTh} {res : List Word}
    {kd : Kid} {R0 : Ty} {T0 : Res} {a : At} {rt : Ty}
    (hR : ThInvRE p (Cut Eg 0 S) (app (f0 R0) th) T0) (hS : SeenLE (Cut Eg 0 S) th.vs.vRelSt)
    (hstk : th.stack = []) (hret : th.term = .ret a) (hev : evalAt th.env a = some (rt, res))
    (hR0 : R0.wf 0 0 = true) (hok : KidOK p R0 kd) :
    TermPtrRts.EnvLbl (EgS Eg) (kidTh th.vs res kd).env := by
  have hp : Eg.prog = p := by
    obtain ⟨_, η, _, _, _, hCE, hE, -⟩ := hR
    exact (congrArg TEnv.prog hCE).symm.trans hE.1
  have kv := kid_val (Eg2 := EgS Eg) (j := 0) (S2 := fun _ => False) hp (InclS_cut_EgS Eg 0 0 _ _) hS
    (vr_of_ret hR hstk hret hev hR0) hok
  have hRL : RLink (Cut (EgS Eg) 0 (fun _ => False)) :=
    RLink_of (Coh_CE (Cut (EgS Eg) 0 (fun _ => False))) (CohR_CE (Cut (EgS Eg) 0 (fun _ => False)))
  have hv := VRR_VR kd.ty hRL kv.1
  have hL := kv.2
  have hwc : wc kd.ty = some (((if kd.useRes then res else []) ++ kd.vals.map cst).map (bumpW th.vs.vRelSt)).length := by
    have h1 := hL.2.2.1
    cases hu : accs kd.ty with
    | none => simp [wc, hu] at h1
    | some us => simp only [wc, hu, Option.map_some]; rw [hL.1 us hu]
  have hl := TermPtrRts.labsIn_pubVR (G := fun l => (EgS Eg).pfr l ≠ none ∨ (EgS Eg).box l ≠ none)
    kd.ty (fun _ => 0) (Cut (EgS Eg) 0 (fun _ => False)) kd.ty _ (fun _ _ _ h => h)
    (fun l f h => Or.inl (by intro h2; change Eg.pfr l = some f at h; change Eg.pfr l = none at h2; rw [h] at h2; cases h2))
    (fun l B h => Or.inr (by intro h2; change Eg.box l = some B at h; change Eg.box l = none at h2; rw [h] at h2; cases h2))
    rfl hwc hL.2.2.2.1 hv
  intro x rt0 ws hm w hw l hn
  simp only [kidTh, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨-, rfl, rfl⟩ := hm
  obtain ⟨a0, g, hva, rfl⟩ := hn
  exact hl w hw a0 g hva

theorem spawnS_phantC {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid} {g : Frame}
    (hth : cs.ths[0]? = some th) : spawnS (phantC g cs) res kids = spawnS cs res kids := by
  have hth' : (phantC g cs).ths[0]? = some (app g th) := by rw [phantC_get]; simp [hth]
  (rw [spawnS_eq hth', spawnS_eq hth, phantC_n]) <;> rfl

theorem pwfAll_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 c : Cfg} (h0 : TermFul.PWFall c0)
    (hr : TermStep.Steps p k arch c0 c) : TermFul.PWFall c := by
  revert h0
  induction hr with
  | refl => exact id
  | step hs _ ih => exact fun h => ih (TermFul.step_pwfAll hs h)

theorem WV_bumpS {n : Nat} {V : Ts} {w : Word} (h : TermViewInv.WV n w) (hV : V ≤ n) :
    TermViewInv.WV n (bumpW V w) :=
  ⟨Nat.max_le.2 ⟨Nat.le_trans h.1 (Nat.le_max_left _ _), Nat.le_max_right _ _⟩, Nat.max_le.2 ⟨h.2, hV⟩⟩

theorem viewInv_spawnS {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid} {a : At} {rt : Ty}
    (hV : TermViewInv.ViewInv cs) (hth : cs.ths[0]? = some th) (hev : evalAt th.env a = some (rt, res)) :
    TermViewInv.ViewInv (spawnS cs res kids) := by
  have hT := hV.2 0 th hth
  have hres := TermViewInv.evalAt_V hT.1 hev
  refine ⟨by rw [spawnS_mem hth]; exact hV.1, fun i t ht => ?_⟩
  obtain ⟨kd, -, rfl⟩ := spawnS_th hth ht
  rw [spawnS_mem hth]
  refine ⟨?_, ⟨fun fr hf => by simp [kidTh] at hf, hT.2.2⟩⟩
  intro e he
  simp only [kidTh, List.mem_singleton] at he
  subst he
  intro w hw
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
  refine WV_bumpS ?_ hT.2.2.2.2.2.2
  rcases List.mem_append.1 hw' with h | h
  · cases hu : kd.useRes
    · rw [hu] at h; cases h
    · rw [hu] at h; exact hres w' h
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 h
    exact ⟨Nat.le_refl _, Nat.zero_le _⟩

theorem pwfAll_spawnS {cs : Cfg} {th : TTh} {res : List Word} {kids : List Kid}
    (hw : TermFul.PWFall cs) (hth : cs.ths[0]? = some th) : TermFul.PWFall (spawnS cs res kids) := by
  intro i
  have hp : TermFul.promsOf (spawnS cs res kids) i = [] := by
    unfold TermFul.promsOf
    cases e : (spawnS cs res kids).ths[i]? with
    | none => rfl
    | some t => simp [spawnS_noProm hth i t e]
  refine ⟨fun q hq => ?_, fun t ht => ?_⟩
  · rw [spawnS_pairs hth] at hq; rw [spawnS_mem hth]; exact (hw 0).1 q hq
  · rw [hp] at ht; cases ht

/-- **The spawn reshape's `SysInvN`, with witnesses** (the body of `startOK_spawnS_proved`'s `H`):
`SysInvN` at `spawnS cs res kids` at `EgS Eg`, where `Eg` carries `OwnLive`/`ObsAll` at the setup end. -/
theorem spawnS_sysInvN_witness {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {cpre cs : Cfg} {th0 th : TTh} {f : String} {ts : List Ty} {d : Decl} {a : At} {rt : Ty} {res : List Word}
    {kids : List Kid}
    (O0 : ObligationsF p k arch Init (fun _ => True) (phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre))
    (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) cpre) (h1 : cpre.ths.size = 1)
    (hpre : cpre.ths[0]? = some th0) (hset : th0.term = .tail f [] (.var "a") ts) (hstk0 : th0.stack = [])
    (hd : p.find f = .ok d)
    (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (hR0a : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hR0w : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true)
    (hrun : TermStep.Steps p k arch cpre cs) (hnp : AllNoProm cs)
    (hth : cs.ths[0]? = some th) (hret : th.term = .ret a) (hstk : th.stack = [])
    (hev : evalAt th.env a = some (rt, res))
    (hkids : kids ≠ []) (hok : ∀ kd ∈ kids, KidOK p (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) kd) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res),
      SysInvN p k arch Init (fun _ => True) (spawnS cs res kids) (EgS Eg) (at0 Tot) (at0 HP) HS
        (fun _ _ => .zero) (fun _ _ => .zero) ∧ OwnLive Eg cs ∧ ObsAll Eg cs := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hOb⟩ :=
    sysInvO_phant_run O0 hk h0 hpre hstk0 hset hd hR0 hR0a hR0w hrun
  have hsz : cs.ths.size = 1 := (steps_size hrun).trans h1
  have hsz' : (phantC (f0 (substTs ts.reverse 0 0 (instT [] 0 d.retTy))) cs).ths.size = 1 :=
    (phantC_size _ _).trans hsz
  have hth' : (phantC (f0 (substTs ts.reverse 0 0 (instT [] 0 d.retTy))) cs).ths[0]? =
      some (app (f0 (substTs ts.reverse 0 0 (instT [] 0 d.retTy))) th) := by
    rw [phantC_get]; simp [hth]
  have hnp' : AllNoProm (phantC (f0 (substTs ts.reverse 0 0 (instT [] 0 d.retTy))) cs) := by
    intro i t ht
    obtain ⟨t0, ht0, rfl | rfl⟩ := phantC_cases ht
    · exact hnp i t0 ht0
    · exact hnp i _ ht0
  obtain ⟨S1, hR1, -, hM1, -⟩ := hN.thr 0 _ hth'
  have H := sysInvN_spawnS (res := res) hN hnp' hsz' hth' hkids hOL
    (fun j hj => hOb j (by rw [hsz']; omega))
    (fun kd hkd S hM hR => kid_both hR hM.2.2.2.2.1 hstk hret hev hR0 (InclS_cut Eg 0 0 _ S) rfl
      (hok kd (List.mem_of_getElem? hkd)) _)
    (fun j kd _ hkd => kid_both hR1 hM1.2.2.2.2.1 hstk hret hev hR0 (InclS_cut_EgS Eg 0 j _ _) rfl
      (hok kd (List.mem_of_getElem? hkd)) _)
    (fun j kd hkd => kid_lbl (th := th) hR1 hM1.2.2.2.2.1 hstk hret hev hR0 (hok kd (List.mem_of_getElem? hkd)))
  rw [spawnS_phantC hth] at H
  refine ⟨Eg, Tot, HP, HS, H, ⟨fun l cl i hs ho => ?_, fun l B hB => ?_⟩, fun j hj => hOb j ?_⟩
  · have := hOL.1 l cl i hs ho; rwa [phantC_size] at this
  · have := hOL.2 l B hB; rwa [phantC_size] at this
  · rw [phantC_size]; exact hj

/-- **`startOK_spawnS`, proved** (with the pending hypotheses `hstk0`, `hstk`, `hR0a`). -/
theorem startOK_spawnS_proved {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {cpre cs : Cfg} {th0 th : TTh} {f : String} {ts : List Ty} {d : Decl} {a : At} {rt : Ty} {res : List Word}
    {kids : List Kid}
    (O0 : ObligationsF p k arch Init (fun _ => True) (phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre))
    (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) cpre) (h1 : cpre.ths.size = 1)
    (hpre : cpre.ths[0]? = some th0) (hset : th0.term = .tail f [] (.var "a") ts) (hstk0 : th0.stack = [])
    (hd : p.find f = .ok d)
    (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (hR0a : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hR0w : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true)
    (hrun : TermStep.Steps p k arch cpre cs) (hnp : AllNoProm cs)
    (hth : cs.ths[0]? = some th) (hret : th.term = .ret a) (hstk : th.stack = [])
    (hev : evalAt th.env a = some (rt, res))
    (hkids : kids ≠ []) (hok : ∀ kd ∈ kids, KidOK p (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) kd) :
    StartOK p k arch Init (fun _ => True) (spawnS cs res kids) := by
  obtain ⟨Eg, Tot, HP, HS, H, -, -⟩ :=
    spawnS_sysInvN_witness O0 hk h0 h1 hpre hset hstk0 hd hR0 hR0a hR0w hrun hnp hth hret hstk hev hkids hok
  have hV := TermViewInv.viewInv_run (TermViewInv.viewInvR_bot (startOK_of_initOK h0).2.2.1) (TermSpawnStep.StepsG.ofSteps hrun)
  have hpw := pwfAll_run ((pwf0_of_initOK h0).resolve_left (by omega)) hrun
  refine ⟨⟨_, _, _, _, _, _, H⟩, spawnS_noProm hth, viewInv_spawnS hV hth hev, Or.inr (pwfAll_spawnS hpw hth)⟩

end TermSpawn

#print axioms TermSpawn.spawnS_sysInvN_witness
#print axioms TermSpawn.startOK_spawnS_proved
