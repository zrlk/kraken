import WeakCore.TermLiveMachE
import WeakCore.TermLiveProv
import WeakCore.ExtArmZ
import WeakCore.SpawnFinalX
import WeakCore.TermLiveHeld
import WeakCore.TermStartW
/-! # TermLiveL3 — mode (B) on the robust branch: setting, scenario starts, hold view (item 37 S1, S3, S7)

The setting of the robust-branch theorems: the EM0 finals' premises at a start `c0`, the frozen start shape
`StartOKX`, and provenance (`ProgTyped`). Provenance is proved, not assumed, at the two kinds of start:
- the wrapper start (`progTyped_startW`, so `setting_of_startW` needs only the finals' premises);
- scenario starts (`TermSpawn.spawnS` after a setup run): the kids carry type arguments and argument types that are
  scenario data, not program text, so provenance holds for `protosOf p ++ kidProtos kids` (`settingM_of_scenarioK`),
  and the scenario-instance theorems are stated over that list (user rule; `sce` applies the same
  robust/epoch check to it).
`SettingM … M` is `Setting` at an arbitrary protocol list `M ⊇ protosOf p`; `Setting` is the instance
`M = protosOf p` (`settingM_of_setting`).

`TouchesW`/`StuckOnW`/`InducedW` are the canonical notions going forward. The TermLiveMach originals over-count loads that read no protocol word through their own type
(`NoWordRead`) and are to be retired in a later cleanup. The held branch must settle `hvI`'s
∃/∀-witness question, given that zero-width references leave a word's Eg typing unpinned. -/

namespace TermLiveL3
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermLiveMach TermProgress
open WeakMem (Arch Address)

/-! ### S1/S7: the setting, and scenario starts -/

/-- The finals' premises at a start `c0` (EM0 relation), the frozen start shape `StartOKX`, and provenance at `c0`. -/
structure Setting (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) (c0 : Cfg) : Prop where
  obl : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
    (fun _ => True) c0
  sdr : k.storeDepRts = true
  start : A9SpawnFinal.StartOKX p k arch Init c0
  prov : ProgTyped p c0

/-- A scenario start: `TermSpawn.spawnS` after a setup run, with exactly the premises of the frozen
`A9SpawnFinal.startOKX_spawnS`. -/
def ScenarioStart (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) (c0 : Cfg) : Prop :=
  ∃ (cpre cs : Cfg) (th0 th : TTh) (f : String) (ts : List Ty) (d : Decl) (a : At) (rt : Ty) (res : List Word)
    (kids : List TermSpawn.Kid),
    TermMain.ObligationsF p k arch Init (fun _ => True)
      (TermSpawn.phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre) ∧
    k.storeDepRts = true ∧ TermMain.InitOK p k arch Init (fun _ => True) cpre ∧ cpre.ths.size = 1 ∧
    cpre.ths[0]? = some th0 ∧ th0.term = .tail f [] (.var "a") ts ∧ th0.stack = [] ∧ p.find f = .ok d ∧
    (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true ∧
    (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true ∧
    TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true ∧
    TermStep.Steps p k arch cpre cs ∧ TermMain.AllNoProm cs ∧ cs.ths[0]? = some th ∧ th.term = .ret a ∧
    th.stack = [] ∧ evalAt th.env a = some (rt, res) ∧ kids ≠ [] ∧
    (∀ kd ∈ kids, TermSpawn.KidOK p (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) kd) ∧
    c0 = TermSpawn.spawnS cs res kids

theorem startOKX_of_scenario {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg}
    (h : ScenarioStart p k arch Init c0) : A9SpawnFinal.StartOKX p k arch Init c0 := by
  obtain ⟨cpre, cs, th0, th, f, ts, d, a, rt, res, kids, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, rfl⟩ := h
  exact A9SpawnFinal.startOKX_spawnS h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19

theorem setting_of_initOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg}
    (O : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hk : k.storeDepRts = true) (h0 : TermMain.InitOK p k arch Init (fun _ => True) c0)
    (hp : ProgTyped p c0) : Setting p k arch Init c0 :=
  ⟨O, hk, A9SpawnFinal.startOKX_of_initOK h0, hp⟩

theorem setting_of_scenario {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg}
    (O : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hS : ScenarioStart p k arch Init c0) (hp : ProgTyped p c0) : Setting p k arch Init c0 :=
  ⟨O, by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h2, _⟩ := hS; exact h2, startOKX_of_scenario hS, hp⟩

/-! ### Start provenance: the wrapper start -/

theorem protosExpr_exitTail (rt : Option Ty) : protosExpr (TermStartW.exitTail rt) = [] := by
  unfold TermStartW.exitTail
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- **Wrapper start provenance.** The wrapper thread names no protocol. -/
theorem progTyped_startW (p : Prog) (cap : Nat) : ProgTyped p (TermStartW.startW p cap) := by
  intro i th h
  obtain ⟨-, rfl⟩ := TermStartW.startW_get h
  unfold ThProv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    simp [TermStartW.wrapTh, TermStartW.wrapTerm, protosExpr, protosOp, protosExpr_exitTail] at hP
  · intro σ hσ; simp [TermStartW.wrapTh] at hσ
  · intro b hb
    simp only [TermStartW.wrapTh, List.mem_singleton] at hb
    subst hb
    intro P hP; cases hP
  · intro f hf; simp [TermStartW.wrapTh] at hf

/-- The wrapper start's `Setting` from the finals' premises alone. -/
theorem setting_of_startW {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {cap : Nat}
    (O : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) (TermStartW.startW p cap)) (hk : k.storeDepRts = true)
    (h0 : TermMain.InitOK p k arch Init (fun _ => True) (TermStartW.startW p cap)) :
    Setting p k arch Init (TermStartW.startW p cap) :=
  setting_of_initOK O hk h0 (progTyped_startW p cap)

/-! ### Start provenance: scenario starts (extended protocol list) -/

/-- The protocols a scenario's kids carry: in their argument types and type arguments (scenario data). -/
def kidProtos (kids : List TermSpawn.Kid) : List Proto :=
  kids.flatMap fun kd => protosTy kd.ty ++ kd.ts.flatMap protosTy

/-- `ScenarioStart` with the kids named: the same premises, in the same order. -/
def ScenarioStartK (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) (kids : List TermSpawn.Kid)
    (c0 : Cfg) : Prop :=
  ∃ (cpre cs : Cfg) (th0 th : TTh) (f : String) (ts : List Ty) (d : Decl) (a : At) (rt : Ty) (res : List Word),
    TermMain.ObligationsF p k arch Init (fun _ => True)
      (TermSpawn.phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre) ∧
    k.storeDepRts = true ∧ TermMain.InitOK p k arch Init (fun _ => True) cpre ∧ cpre.ths.size = 1 ∧
    cpre.ths[0]? = some th0 ∧ th0.term = .tail f [] (.var "a") ts ∧ th0.stack = [] ∧ p.find f = .ok d ∧
    (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true ∧
    (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true ∧
    TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true ∧
    TermStep.Steps p k arch cpre cs ∧ TermMain.AllNoProm cs ∧ cs.ths[0]? = some th ∧ th.term = .ret a ∧
    th.stack = [] ∧ evalAt th.env a = some (rt, res) ∧ kids ≠ [] ∧
    (∀ kd ∈ kids, TermSpawn.KidOK p (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) kd) ∧
    c0 = TermSpawn.spawnS cs res kids

theorem scenarioStart_iff {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg} :
    ScenarioStart p k arch Init c0 ↔ ∃ kids, ScenarioStartK p k arch Init kids c0 := by
  constructor
  · rintro ⟨cpre, cs, th0, th, f, ts, d, a, rt, res, kids, h⟩
    exact ⟨kids, cpre, cs, th0, th, f, ts, d, a, rt, res, h⟩
  · rintro ⟨kids, cpre, cs, th0, th, f, ts, d, a, rt, res, h⟩
    exact ⟨cpre, cs, th0, th, f, ts, d, a, rt, res, kids, h⟩

/-- **Scenario start provenance.** The kids of `spawnS` name only `kidProtos kids`. -/
theorem progTypedM_spawnS {M : List Proto} {cs : Cfg} {res : List Word} {kids : List TermSpawn.Kid} {th : TTh}
    (hth : cs.ths[0]? = some th) (hk : ∀ P ∈ kidProtos kids, P ∈ M) :
    ProgTypedM M (TermSpawn.spawnS cs res kids) := by
  intro i t h
  simp only [TermSpawn.spawnS, hth, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨kd, hkd, rfl⟩ := h
  have hm : kd ∈ kids := List.mem_of_getElem? hkd
  have hk' : ∀ P, P ∈ protosTy kd.ty ++ kd.ts.flatMap protosTy → P ∈ M :=
    fun P hP => hk P (List.mem_flatMap.2 ⟨kd, hm, hP⟩)
  unfold ThProvM
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    simp only [TermSpawn.kidTh, protosExpr] at hP
    exact hk' P (List.mem_append_right _ hP)
  · intro σ hσ; simp [TermSpawn.kidTh] at hσ
  · intro b hb
    simp only [TermSpawn.kidTh, List.mem_singleton] at hb
    subst hb
    exact fun P hP => hk' P (List.mem_append_left _ hP)
  · intro f hf; simp [TermSpawn.kidTh] at hf

/-- `Setting` at an arbitrary protocol list `M` containing the program's: the setting of the scenario instances. -/
structure SettingM (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) (M : List Proto) (c0 : Cfg) :
    Prop where
  obl : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
    (fun _ => True) c0
  sdr : k.storeDepRts = true
  start : A9SpawnFinal.StartOKX p k arch Init c0
  prov : ProgTypedM M c0
  sub : ∀ P ∈ protosOf p, P ∈ M

theorem settingM_of_setting {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg}
    (S : Setting p k arch Init c0) : SettingM p k arch Init (protosOf p) c0 :=
  ⟨S.obl, S.sdr, S.start, S.prov, fun _ h => h⟩

/-- **Scenario setting.** At a scenario start, the setting holds for `protosOf p ++ kidProtos kids`, from the finals'
obligations and the scenario premises alone (no provenance hypothesis). -/
theorem settingM_of_scenarioK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res}
    {kids : List TermSpawn.Kid} {c0 : Cfg}
    (O : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hS : ScenarioStartK p k arch Init kids c0) :
    SettingM p k arch Init (protosOf p ++ kidProtos kids) c0 := by
  have hS' : ScenarioStart p k arch Init c0 := scenarioStart_iff.2 ⟨kids, hS⟩
  obtain ⟨_, cs, _, th, _, _, _, _, _, res, _, h2, _, _, _, _, _, _, _, _, _, _, _, h14, _, _, _, _, _, rfl⟩ := hS
  exact ⟨O, h2, startOKX_of_scenario hS', progTypedM_spawnS h14 (fun P hP => List.mem_append_right _ hP),
    fun P hP => List.mem_append_left _ hP⟩

/-! ### S3: the hold view -/

/-- `b` is a non-ghost word of protocol `P` naming region `n` in the global environment `Eg`. -/
def WordAtG (Eg : TermCut.GEnv) (b : Address) (n : Nat) (P : Proto) : Prop :=
  ∃ cl, Eg.sto b.label = some cl ∧ TermSound.AtOff cl.ty b.offset (.word (.lit n) P) ∧ P.ghost = false

/-- `heldAt`: for some invariant witness, `b` is a word of `P` (region `n`) whose latest value is in a held state.
`holder`: for some invariant witness, thread `h`'s bound carries region token `rg n`. -/
def hvI (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) : HoldView where
  heldAt c b n P := ∃ Eg Tot HP HS cr db, TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
    WordAtG Eg b n P ∧ ∃ v, Latest c b v ∧ TermLiveHeld.HeldV P v
  holder c _ n h := ∃ Eg Tot HP HS cr db, TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
    1 ≤ Tot h (.rg n)

/-! ### S4: inversion at a touched word (G-L2) -/


section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermLiveMach
open WeakMem (Arch Address)

/-- The head is a `load` that reads no protocol word through its own type: its reference is not a pointer to a
non-ghost word (typed non-word loads read deep word-free data; a torn load's value is quarantined in `cx.torn` until
the seq check, which is a word access; a ghost word has no units, so its load reads nothing). -/
def NoWordRead (th : TTh) : Prop :=
  ∃ x acq a e t pw, th.term = .let_ x (.load acq a) e ∧ evalAt th.env a = some (t, [pw]) ∧
    ∀ r P, wordOf t = some (r, P) → P.ghost = true

/-! ### Static and runtime pointees -/

/-- The cell a reference's runtime word points at holds the closed static pointee at the word's offset. -/
theorem inv_target_cell {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {w : At} {tw u t : Ty}
    {μ : Mode} {pw : Word} {b : Address}
    (hv : VarsOK ρ η σs cx.vars env) (hpk : cx.peek w = .ok tw) (hc : cellOf tw = some (μ, u))
    (hacc : accs (cl ρ η.wit 0 0 u) ≠ none) (hea : evalAt env w = some (t, [pw])) (hA : addrOf pw = some b) :
    ∃ c, η.sto b.label = some c ∧ AtOff c.ty b.offset (cl ρ η.wit 0 0 u) ∧
      IniAt η.ini c b (cl ρ η.wit 0 0 u) := by
  obtain ⟨rt', ws, hea', hvr, -⟩ := peek_VR hv hpk
  rw [hea] at hea'
  cases hea'
  obtain ⟨ad, c, hws, hsto, hat, -, hini⟩ := cell_target hc (Fd_noarr hacc) hvr
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have hb : b = ad := by
    simp only [addrOf, hws] at hA
    cases hA; rfl
  subst hb
  exact ⟨c, hsto, hat, IniAt_mono (modeIni_le_ini _ _ _) hini⟩

theorem inv_close_word {σs : List Ty} {u : Ty} {r : Idx} {P : Proto} (h : close σs u = .word r P) :
    (∃ r0, u = .word r0 P) ∨ ∃ k, u = .tvar k ∧ σs[k]? = some (.word r P) := by
  cases u with
  | word r0 P0 =>
      simp only [close, substTs, Ty.word.injEq] at h
      exact .inl ⟨r0, by rw [h.2]⟩
  | tvar k =>
      right
      refine ⟨k, rfl, ?_⟩
      simp only [close, substTs, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at h
      split at h
      · rename_i σ hσ
        simp only [shiftIN, shiftTN] at h
        rw [hσ, h]
      · cases h
  | _ => simp [close, substTs] at h

theorem inv_esig_word {T : Ty} {r : Idx} {P : Proto} (h : er (skel T) = .word r P) : ∃ r', T = .word r' P := by
  cases T <;> simp [skel, er] at h
  case word r' P' => exact ⟨r', by rw [h.2]⟩
  case refine t ψ => unfold rf at h; split at h <;> simp [er] at h

/-- The runtime reference's pointee skeleton is the closed static pointee's. -/
theorem inv_runtime_word {σs : List Ty} {rt tw u : Ty} {μ : Mode} {r : Idx} {P : Proto}
    (hl : etok (skel rt) = etok (skel (close σs tw))) (hc : cellOf tw = some (μ, u))
    (hwt : wordOf rt = some (r, P)) : etok (skel (close σs u)) = .word (.lit 0) P := by
  obtain ⟨μ', hrt⟩ := wordOf_cases hwt
  rcases cell_cases hc with rfl | rfl <;> rcases hrt with rfl | rfl <;>
    simp [close, substTs, skel, etok] at hl ⊢ <;> exact hl.2.symm

/-- A static word pointee has a runtime word pointee of the same protocol. -/
theorem inv_static_word {σs : List Ty} {rt tw : Ty} {r : Idx} {P : Proto}
    (hl : etok (skel rt) = etok (skel (close σs tw))) (hwd : wordOf tw = some (r, P)) :
    ∃ r', wordOf rt = some (r', P) := by
  obtain ⟨μ, htw⟩ := wordOf_cases hwd
  rcases htw with rfl | rfl
  · simp only [close, substTs, skel, etok] at hl
    obtain ⟨μ', u', rfl, -, hu⟩ := eskel_eq_ptr hl
    obtain ⟨r', rfl⟩ := eskel_word hu
    exact ⟨r', rfl⟩
  · simp only [close, substTs, skel, etok] at hl
    obtain ⟨μ', u', rfl, -, hu⟩ := eskel_eq_loc hl
    obtain ⟨r', rfl⟩ := eskel_word hu
    exact ⟨r', rfl⟩

/-- The closed static pointee of a reference whose runtime pointee is a word is that word. -/
theorem inv_cl_word {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {u : Ty} {P : Proto}
    (hW : WitL σs η.wit cx.opq) (hsk : etok (skel (close σs u)) = .word (.lit 0) P) :
    ∃ r1, cl ρ η.wit 0 0 u = .word r1 P := by
  obtain ⟨r2, hcw⟩ := eskel_word hsk
  rcases inv_close_word hcw with ⟨r0, rfl⟩ | ⟨k, rfl, hσ⟩
  · exact ⟨clI ρ 0 r0, by simp [cl]⟩
  · have hk : k ∉ cx.opq := fun hm => by
      have := (hW.2.1 k _ hσ).2 hm
      cases this
    have hlt : k < σs.length := (List.getElem?_eq_some_iff.1 hσ).1
    have h1 := hW.1 k hk hlt
    have hck : close σs (.tvar k) = .word r2 P := by
      simp only [close, substTs, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, hσ, shiftIN, shiftTN]
    rw [hck] at h1
    have h2 : er (skel (η.wit k)) = .word (.lit 0) P := by
      rw [← sig, ← h1]; simp [sig, skel, er]
    obtain ⟨r', hr'⟩ := inv_esig_word h2
    exact ⟨r', by simp [cl, hr']⟩

theorem inv_protos_word {t : Ty} {r : Idx} {P : Proto} (h : wordOf t = some (r, P)) : P ∈ protosTy t := by
  obtain ⟨μ, ht⟩ := wordOf_cases h
  rcases ht with rfl | rfl <;> simp [protosTy]

/-- **Word target.**  A reference whose runtime pointee is a non-ghost word of protocol `P'` reaches, at its
word's address, a word of protocol `P'`: any non-ghost word there is of `P'`. -/
theorem inv_word_target {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {tw u t : Ty} {μ : Mode} {pw : Word} {b : Address} {r' : Idx} {P' : Proto} {n : Nat}
    {P : Proto}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek w = .ok tw) (hc : cellOf tw = some (μ, u))
    (hea : evalAt env w = some (t, [pw])) (hwt : wordOf t = some (r', P')) (hg' : P'.ghost = false)
    (hA : addrOf pw = some b)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    P ∈ protosTy t := by
  obtain ⟨rt, ws, hea', -, hl⟩ := peek_VR hi.2.1 hpk
  rw [hea] at hea'
  cases hea'
  obtain ⟨r1, hcl⟩ := inv_cl_word (ρ := ρ) hi.2.2.2.1 (inv_runtime_word hl.2.1 hc hwt)
  obtain ⟨c, hsto, hat, -⟩ := inv_target_cell hi.2.1 hpk hc (by rw [hcl]; simp [accs, hg']) hea hA
  rw [hcl] at hat
  obtain ⟨-, rfl⟩ := AtOff_word_uniq hg hg' (hw c hsto) hat
  exact inv_protos_word hwt

/-! ### The access forms -/

/-- The heads `targetOf` names. -/
theorem inv_target_cases {th : TTh} {w : At} (h : targetOf th = some w) :
    (∃ acq rel e v x ok fail, th.term = .cas acq rel w e v x ok fail) ∨
    (∃ acq rel e0 e1 v0 v1 x ok fail, th.term = .casp acq rel w e0 e1 v0 v1 x ok fail) ∨
    (∃ x acq e, th.term = .let_ x (.load acq w) e) ∨
    (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w v) e) ∨
    (∃ x acq n0 n1 e, th.term = .let_ x (.ldp acq w n0 n1) e) := by
  unfold targetOf at h
  split at h
  · cases h; exact .inl ⟨_, _, _, _, _, _, _, ‹_›⟩
  · cases h; exact .inr (.inl ⟨_, _, _, _, _, _, _, _, _, ‹_›⟩)
  · cases h; exact .inr (.inr (.inl ⟨_, _, _, ‹_›⟩))
  · cases h; exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, ‹_›⟩)))
  · cases h; exact .inr (.inr (.inr (.inr ⟨_, _, _, _, _, ‹_›⟩)))
  · cases h

theorem inv_cell_of_word {t : Ty} {r : Idx} {P : Proto} (h : wordOf t = some (r, P)) :
    ∃ μ, cellOf t = some (μ, .word r P) := by
  obtain ⟨μ, ht⟩ := wordOf_cases h
  exact ⟨μ, by rcases ht with rfl | rfl <;> rfl⟩

/-- (`pwf_of_held` for any word, ghost or not) A word component of a cell that also has a non-ghost word at the
same offset has a well-formed protocol: memory's holding records the cell's value (`VRR` at `word`). -/
theorem inv_pwf_held {η : TEnv} {s : St} {H : Res} {A : Address} {c : Cell} {n n' : Nat} {P Q : Proto}
    (hH : MemHeld (CE η) s H) (hsto : η.sto A.label = some c) (hat : AtOff c.ty A.offset (.word (.lit n) Q))
    (hini : IniAt η.ini c A (.word (.lit n) Q)) (hatP : AtOff c.ty A.offset (.word (.lit n') P))
    (hg : P.ghost = false) : pwf Q = true := by
  obtain ⟨R0, H0, -, hent0, -⟩ := MemHeld_focus hH A.label
  obtain ⟨vals0, -, hC0⟩ := hent0.2 c hsto
  have hna : ∀ N e, Ty.word (.lit n) Q ≠ .array (.lit N) e := fun N e h => by cases h
  rcases own_segR hC0 hat hini hna with ⟨b, oS, S, wS, Rsg, Rrc, -, -, hatS, hwS, hbw, -, ⟨hvs, -⟩, -⟩ |
    ⟨N, e, us, hT, hus, hn, -, -⟩
  · have hsl : ((vals0.drop b).take wS).length = wS := by
      simp only [List.length_take, List.length_drop]; omega
    obtain ⟨n1, Rq, Rr2, -, -, -, hvq, -⟩ := VRR_at (CE η).unsee hatS hvs (by rw [hsl]; exact hwS)
    simp only [VRR] at hvq
    exact hvq.1.1
  · rw [hT] at hatP
    rcases AtOff_array_inv (fun _ h => by cases h) hatP with ⟨-, h⟩ | ⟨N', j, o2, us', hN, hus', -, -, hat2⟩
    · cases h
    · rw [hus] at hus'
      cases hus'
      have := AtOff_bound hat2 hus (accs_word hg)
      rw [hn] at this; simp [nWords, Acc.size] at this

/-- A word access whose static protocol is non-ghost: the runtime pointee is that word. -/
theorem inv_word_access {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {tw t : Ty} {pw : Word} {b : Address} {r0 : Idx} {P0 : Proto} {n : Nat} {P : Proto}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek w = .ok tw) (hwd : wordOf tw = some (r0, P0))
    (hg0 : P0.ghost = false) (hea : evalAt env w = some (t, [pw])) (hA : addrOf pw = some b)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    P ∈ protosTy t := by
  obtain ⟨rt, ws, hea', -, hl⟩ := peek_VR hi.2.1 hpk
  rw [hea] at hea'
  cases hea'
  obtain ⟨r', hwt⟩ := inv_static_word hl.2.1 hwd
  obtain ⟨μ, hc⟩ := inv_cell_of_word hwd
  exact inv_word_target hi hpk hc hea hwt hg0 hA hw hg

/-- An epoch-counter access (`casEpoch`, `fetchEpoch`): the counter is non-ghost (`pwf`, from memory), so as
`inv_word_access`. -/
theorem inv_epoch_access {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {s : St} {H : Res} {w : At} {tw t : Ty} {pw : Word} {b : Address} {r0 : Idx} {P0 : Proto}
    {n : Nat} {P : Proto}
    (hi : FInv ρ η σs K cx env) (hH : MemHeld (CE η) s H) (hpk : cx.peek w = .ok tw)
    (hwd : wordOf tw = some (r0, P0)) (hep : P0.epoch = true)
    (hea : evalAt env w = some (t, [pw])) (hA : addrOf pw = some b)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    P ∈ protosTy t := by
  have hg0 : P0.ghost = false := by
    cases hq : P0.ghost with
    | false => rfl
    | true =>
        obtain ⟨μ, hc⟩ := inv_cell_of_word hwd
        obtain ⟨c, hsto, hat, hini⟩ := inv_target_cell hi.2.1 hpk hc (by simp [cl, accs, hq]) hea hA
        simp only [cl, clI_zero] at hat hini
        have hpwf := inv_pwf_held hH hsto hat hini (hw c hsto) hg
        rw [pwf_epoch_ghost hpwf hep] at hq
        cases hq
  exact inv_word_access hi hpk hwd hg0 hea hA hw hg

/-- A pair access never reaches a non-ghost word. -/
theorem inv_word2_access {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {tw t : Ty} {pw : Word} {b : Address} {r0 : Idx} {P0 : Proto2} {n : Nat} {P : Proto}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek w = .ok tw) (hwd : word2Of tw = some (r0, P0))
    (hea : evalAt env w = some (t, [pw])) (hA : addrOf pw = some b)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    False := by
  obtain ⟨c, hsto, hat⟩ := TermLiveHeld.word2_link hi.2.1 hpk hwd hea hA
  rcases AtOff_word_word2 hg (hw c hsto) hat with h | h <;> omega

/-- An epoch-pair access never reaches a non-ghost word. -/
theorem inv_epair_access {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {tw t : Ty} {pw : Word} {b : Address} {r0 : Idx} {P0 : ECounter} {n : Nat} {P : Proto}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek w = .ok tw) (hwd : epairOf tw = some (r0, P0))
    (hea : evalAt env w = some (t, [pw])) (hA : addrOf pw = some b)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    False := by
  have hcell : ∃ μ, cellOf tw = some (μ, .epair r0 P0) := by
    unfold epairOf at hwd
    split at hwd <;> cases hwd <;> exact ⟨_, rfl⟩
  obtain ⟨μ, hcell⟩ := hcell
  obtain ⟨c, hsto, hat, -⟩ := inv_target_cell hi.2.1 hpk hcell (by simp [cl, accs]) hea hA
  simp only [cl, clI_zero] at hat
  have hS : Solid (.epair (.lit (ev ρ r0)) P0) :=
    ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ h => by cases h)⟩
  have hus : accs (.epair (.lit (ev ρ r0)) P0) = some [.two] := by simp [accs]
  exact TermLiveHeld.solid_no_word (j := 0) hsto hat hS (fun _ _ h => by cases h) hus rfl (by simp)
    (by simp [nWords, Acc.size]) ⟨c, hsto, hw c hsto, hg⟩

/-- A one-word non-affine cell access (`casCell`, `fetchCell`) never reaches a non-ghost word. -/
theorem inv_plain_access {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {w : At} {tw u t : Ty} {μ : Mode} {pw : Word} {b : Address} {n : Nat} {P : Proto}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx) (hpk : cx.peek w = .ok tw)
    (hcw : cellOf tw = some (μ, u)) (hone : u.rawWords = some 1) (haff : affine cx.ke u = false)
    (hea : evalAt env w = some (t, [pw])) (hA : addrOf pw = some b)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    False := by
  obtain ⟨rt, pw', ad, c, hea', hpw, hsto, hat, -, hdw⟩ :=
    plainTarget hi hE hpk hcw hone haff (tb_cellOf (peek_tb htv hpk) hcw)
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨-, rfl⟩ := hea'
  have hb : b = ad := by simp only [addrOf, hpw, Option.some.injEq] at hA; exact hA.symm
  subst hb
  exact TermLiveHeld.dwf_no_word (j := 0) hsto hat hdw (accs_cl_one hone) rfl (by simp)
    (by simp [TermLiveHeld.nW_one]) ⟨c, hsto, hw c hsto, hg⟩

/-- A load whose runtime reference is to a non-ghost word. -/
theorem inv_load_access {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {tw u t : Ty} {μ : Mode} {pw : Word} {b : Address} {n : Nat} {P : Proto}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek w = .ok tw) (hc : cellOf tw = some (μ, u))
    (hea : evalAt env w = some (t, [pw])) (hA : addrOf pw = some b)
    (hwl : ∃ r Q, wordOf t = some (r, Q) ∧ Q.ghost = false)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    P ∈ protosTy t := by
  obtain ⟨r, Q, hwt, hgq⟩ := hwl
  exact inv_word_target hi hpk hc hea hwt hgq hA hw hg

/-- **Frame form.**  The protocol of a non-ghost word at the address a typed thread's access head touches is in
the runtime type of the touching reference, unless the head is a load whose reference is not to a non-ghost word. -/
theorem touched_inv_core {p : Prog} {ρ : Nat → Nat} {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx}
    {th : TTh} {s : St} {H : Res} {w : At} {t : Ty} {pw : Word} {b : Address} {n : Nat} {P : Proto}
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx) (hH : MemHeld (CE η) s H)
    (hT : Typed p cx th.term)
    (htg : targetOf th = some w) (hea : evalAt th.env w = some (t, [pw])) (hA : addrOf pw = some b)
    (hld : ∀ x acq e, th.term = .let_ x (.load acq w) e → ∃ r Q, wordOf t = some (r, Q) ∧ Q.ghost = false)
    (hw : ∀ c, η.sto b.label = some c → AtOff c.ty b.offset (.word (.lit n) P)) (hg : P.ghost = false) :
    P ∈ protosTy t := by
  rcases inv_target_cases htg with ⟨acq, rel, e, v, x, ok, fail, hte⟩ |
    ⟨acq, rel, e0, e1, v0, v1, x, ok, fail, hte⟩ | ⟨x, acq, e, hte⟩ | ⟨x, o, acq, rel, v, e, hte⟩ |
    ⟨x, acq, n0, n1, e, hte⟩
  · rw [hte] at hT
    cases hT with
    | casCell hpk _ hc hone haff =>
        rcases hc with hc | ⟨_, hc, _⟩ <;> exact (inv_plain_access hi hE htv hpk hc hone haff hea hA hw hg).elim
    | casShare hpk hwd hg0 => exact inv_word_access hi hpk hwd hg0 hea hA hw hg
    | casTake hpk hwd hg0 => exact inv_word_access hi hpk hwd hg0 hea hA hw hg
    | casEpoch hpk hwd hep => exact inv_epoch_access hi hH hpk hwd hep hea hA hw hg
  · rw [hte] at hT
    cases hT with
    | caspE hpk _ hep => exact (inv_epair_access hi hpk hep hea hA hw hg).elim
    | caspBump hpk hwd => exact (inv_word2_access hi hpk hwd hea hA hw hg).elim
    | caspMove hpk hwd => exact (inv_word2_access hi hpk hwd hea hA hw hg).elim
    | caspTake hpk hwd => exact (inv_word2_access hi hpk hwd hea hA hw hg).elim
  · have hwl := hld x acq e hte
    rw [hte] at hT
    cases hT with
    | let_ hop _ =>
      cases hop with
      | loadWord hpk hwd =>
          obtain ⟨μ, hc⟩ := inv_cell_of_word hwd
          exact inv_load_access hi hpk hc hea hA hwl hw hg
      | loadOwn hpk _ hc => exact inv_load_access hi hpk hc hea hA hwl hw hg
      | loadPub hpk _ hc => exact inv_load_access hi hpk hc hea hA hwl hw hg
      | loadRgn hpk _ hc => exact inv_load_access hi hpk hc hea hA hwl hw hg
      | loadCap hpk _ hc => exact inv_load_access hi hpk hc hea hA hwl hw hg
      | loadTorn hpk _ hc => exact inv_load_access hi hpk hc hea hA hwl hw hg
  · rw [hte] at hT
    cases hT with
    | let_ hop _ =>
      cases hop with
      | fetchCell hpk _ hc =>
          have hone : Ty.int.rawWords = some 1 := by first | rfl | simp [Ty.rawWords]
          have haff : affine cx.ke .int = false := by first | rfl | simp [affine]
          rcases hc with hc | ⟨_, hc, _⟩ <;> exact (inv_plain_access hi hE htv hpk hc hone haff hea hA hw hg).elim
      | fetchEpoch hpk hwd hep => exact inv_epoch_access hi hH hpk hwd hep hea hA hw hg
      | fetchShare hpk hwd _ _ _ hok =>
          exact inv_word_access hi hpk hwd (TermLiveHeld.fetchOK_facts hok).1 hea hA hw hg
  · rw [hte] at hT
    cases hT with
    | let_ hop _ =>
      cases hop with
      | ldp hpk hpr =>
          simp only [pairRef, Bool.or_eq_true, Option.isSome_iff_exists] at hpr
          rcases hpr with ⟨⟨r0, P0⟩, hwd⟩ | ⟨⟨r0, P0⟩, hep⟩
          · exact (inv_word2_access hi hpk hwd hea hA hw hg).elim
          · exact (inv_epair_access hi hpk hep hea hA hw hg).elim

/-! ### The machine form -/

/-- **Inversion at a touched word.** For every invariant witness, a word of protocol `P` at the address that a thread's
head accesses (other than a `NoWordRead` load) has `P` in the access's runtime type. -/
theorem touched_inv {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c : Cfg}
    {Eg : TermCut.GEnv} {Tot HP : Nat → TermSound.Res} {HS : TermSound.Res} {cr db : Nat → WeakMem.Ts → TermSound.Res}
    (hN : TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db)
    {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) {w : At} (htg : TermLiveMach.targetOf th = some w)
    {t : Ty} {pw : Word} (hea : evalAt th.env w = some (t, [pw])) {b : Address} (hA : addrOf pw = some b)
    (hnz : ¬ NoWordRead th) {n : Nat} {P : Proto} (hw : WordAtG Eg b n P) : P ∈ protosTy t := by
  obtain ⟨S, hS⟩ := hN.thr i th hth
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, -, hE, hT, htv, hFR, -, -, -, hH, -⟩ := TermMain.ThSysAt.env (S := S) hN.clo hS
  obtain ⟨cl0, hcl0, hat0, hg⟩ := hw
  have hld : ∀ x acq e, th.term = .let_ x (.load acq w) e → ∃ r Q, wordOf t = some (r, Q) ∧ Q.ghost = false :=
    fun x acq e hte => by
      cases hwt : wordOf t with
      | none => exact (hnz ⟨x, acq, w, e, t, pw, hte, hea, fun r Q h => by rw [hwt] at h; cases h⟩).elim
      | some rQ =>
          cases hq : rQ.2.ghost with
          | false => exact ⟨rQ.1, rQ.2, rfl, hq⟩
          | true =>
              exact (hnz ⟨x, acq, w, e, t, pw, hte, hea, fun r Q h => by
                rw [hwt] at h; cases h; exact hq⟩).elim
  have hw' : ∀ c', η.sto b.label = some c' → AtOff c'.ty b.offset (.word (.lit n) P) := fun c' hc' => by
    have h1 : (CE η).sto b.label = some c' := hc'
    rw [hCE, Cut_sto, cutSto_some] at h1
    rw [h1.1] at hcl0
    cases hcl0
    exact hat0
  exact touched_inv_core hFR.1 hE htv hH hT.1 htg hea hA hld hw' hg

/-- The runtime type of an operand is a binding's type (or a literal's or `()`'s, which name no protocol), so its
protocols are among those `ThProvM M` allows. -/
theorem touched_inv_mem {M : List Proto} {th : TTh} {w : At} {t : Ty} {ws : List Word} {P : Proto}
    (hprov : ThProvM M th) (hea : evalAt th.env w = some (t, ws)) (hP : P ∈ protosTy t) : P ∈ M := by
  cases w with
  | var x =>
      simp only [evalAt, lookupE, Option.map_eq_some_iff] at hea
      obtain ⟨bd, hbd, hb⟩ := hea
      have hmem : bd ∈ th.env := List.mem_of_find?_eq_some hbd
      exact hprov.2.2.1 bd hmem P (by rw [hb]; exact hP)
  | lit m =>
      simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at hea
      obtain ⟨rfl, -⟩ := hea
      simp [protosTy] at hP
  | unit =>
      simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at hea
      obtain ⟨rfl, -⟩ := hea
      simp [protosTy] at hP

end

/-! ### S4/S5: word reads and the robust-branch statements (G-L2) -/

section
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermLiveMach TermProgress
open WeakMem (Arch Address)

/-! ### Word reads: `TouchesW`, `StuckOnW`, `InducedW` -/

/-- `Touches` without `NoWordRead` loads: a head that accesses `b` and, if it is a load, reads a non-ghost word through
its own type. -/
def TouchesW (c : Cfg) (i : Nat) (b : Address) : Prop :=
  Touches c i b ∧ ∀ th, c.ths[i]? = some th → ¬ NoWordRead th

/-- `StuckOn` with `TouchesW` for `Touches`. -/
def StuckOnW (sys : LSys) (r : LRun sys.L) (i : Nat) (b : Address) : Prop :=
  (∃ n₀ v, ∀ n, n₀ ≤ n → Latest (r.cfg n) b v) ∧
  Often (fun n => r.lbl n = some (sys.thr i)) ∧
  Often (fun n => TouchesW (r.cfg n) i b)

/-- `Induced` with `StuckOnW` for `StuckOn`: the stuck thread reads the held word itself. -/
def InducedW (sys : LSys) (hv : HoldView) (r : LRun sys.L) (D : Nat → Option Nat) : Prop :=
  ∃ i b n P h, Live r D i ∧ StuckOnW sys r i b ∧ Ev (fun m => hv.heldAt (r.cfg m) b n P) ∧
    Ev (fun m => hv.holder (r.cfg m) b n h) ∧ D h ≠ none

theorem touchesW_touches {c : Cfg} {i : Nat} {b : Address} (h : TouchesW c i b) : Touches c i b := h.1
theorem stuckOnW_stuckOn {sys : LSys} {r : LRun sys.L} {i : Nat} {b : Address} (h : StuckOnW sys r i b) :
    StuckOn sys r i b := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun m => ?_⟩
  obtain ⟨n, hn, ht⟩ := h3 m
  exact ⟨n, hn, ht.1⟩
theorem inducedW_induced {sys : LSys} {hv : HoldView} {r : LRun sys.L} {D : Nat → Option Nat}
    (h : InducedW sys hv r D) : Induced sys hv r D := by
  obtain ⟨i, b, n, P, h, h1, h2, h3, h4, h5⟩ := h
  exact ⟨i, b, n, P, h, h1, stuckOnW_stuckOn h2, h3, h4, h5⟩

/-! ### S4/S5: statements -/

/-- **S4** at an arbitrary protocol list `M`: on a run from a `SettingM … M` start, a word that a thread is about to
access has a protocol in `M`, for every invariant witness. -/
theorem touched_mentionedM {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {M : List Proto}
    {c0 : Cfg} (S : SettingM p k arch Init M c0) {c : Cfg} (hr : StepsE p k arch c0.cap c0 c)
    {Eg : TermCut.GEnv} {Tot HP : Nat → TermSound.Res} {HS : TermSound.Res} {cr db : Nat → WeakMem.Ts → TermSound.Res}
    (hN : TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db)
    {i : Nat} {b : Address} (ht : TouchesW c i b) {n : Nat} {P : Proto} (hw : WordAtG Eg b n P) :
    P ∈ M := by
  obtain ⟨⟨th, w, t, pw, hth, htg, hea, hA⟩, hnz⟩ := ht
  have hprov := progTypedM_stepsE S.sub S.prov hr i th hth
  exact touched_inv_mem hprov hea (touched_inv hN hth htg hea hA (hnz th hth) hw)

/-- **S4.** On a run from a `Setting` start, a word that a thread is about to access has a protocol the program names,
for every invariant witness. -/
theorem touched_mentioned {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg}
    (S : Setting p k arch Init c0) {c : Cfg} (hr : StepsE p k arch c0.cap c0 c)
    {Eg : TermCut.GEnv} {Tot HP : Nat → TermSound.Res} {HS : TermSound.Res} {cr db : Nat → WeakMem.Ts → TermSound.Res}
    (hN : TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db)
    {i : Nat} {b : Address} (ht : TouchesW c i b) {n : Nat} {P : Proto} (hw : WordAtG Eg b n P) :
    P ∈ protosOf p :=
  touched_mentionedM (settingM_of_setting S) hr hN ht hw

/-- Every protocol `Mentioned` names is `robust` and `pwf`, or `pwf` and an epoch counter (`robust_noHeld`,
`epoch_facts`: either gives `NoHeld`). -/
def ProgRobustPwf (Mentioned : Proto → Prop) : Prop :=
  ∀ P, Mentioned P → (P.robust = true ∧ pwf P = true) ∨ (pwf P = true ∧ P.epoch = true)

/-- **No held-word-induced livelock** (not "no livelock": frozen-memory spins the program chooses are not excluded).
`no_induced_livelock_robust` with `ProgRobustPwf`, and without the antecedents the (static) robust proof does not use:
`CfgCoh c₀`, `∀ n, ResNonAffine`, `CrashOK`, `Fair`. Stuck threads are those that read the held word
(`StuckOnW`). A load that reads no protocol word through its own type (`NoWordRead`) is not counted. -/
def no_induced_livelock_robust2 (sys : LSys) (Setting : Cfg → Prop) (Mentioned : Proto → Prop)
    (hv : HoldView) : Prop :=
  ∀ c₀, Setting c₀ → ProgRobustPwf Mentioned →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat), sys.Run r → r.cfg 0 = c₀ → ¬ InducedW sys hv r D

/-- The robust branch's content (touched form): no word that a thread is about to access is ever in a held state. -/
def robust_touchedFree (sys : LSys) (Setting : Cfg → Prop) (Mentioned : Proto → Prop) (hv : HoldView) : Prop :=
  ∀ c₀, Setting c₀ → ProgRobustPwf Mentioned →
  ∀ (r : LRun sys.L), sys.Run r → r.cfg 0 = c₀ → ∀ m i b n P, TouchesW (r.cfg m) i b → ¬ hv.heldAt (r.cfg m) b n P

/-- A pwf protocol that is robust or an epoch counter has no held value. -/
theorem not_heldV_of_robustPwf {P : Proto} (h : (P.robust = true ∧ pwf P = true) ∨ (pwf P = true ∧ P.epoch = true))
    (v : WeakMem.Val) : ¬ TermLiveHeld.HeldV P v := by
  rcases h with ⟨hrob, hpwf⟩ | ⟨hpwf, hep⟩
  · exact TermLiveHeld.robust_held_static hpwf hrob v
  · exact (TermLiveHeld.epoch_facts hpwf hep).2.not_heldV v

/-- **S5a** at an arbitrary protocol list `M`. -/
theorem robust_touchedFreeM (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) (M : List Proto) :
    robust_touchedFree (machineE p k arch) (SettingM p k arch Init M) (· ∈ M) (hvI p k arch Init) := by
  intro c₀ S hR r hr h0 m i b n P ht hheld
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hw, v, -, hv⟩ := hheld
  have hst := (machineE_run_stepsE hr m).1
  rw [h0] at hst
  exact not_heldV_of_robustPwf (hR P (touched_mentionedM S hst hN ht hw)) v hv

/-- From the touched form to no held-word-induced livelock: `InducedW` needs the touched word held from some point
on, and touched (`TouchesW`) infinitely often. -/
theorem no_induced_of_touchedFree {sys : LSys} {Setting : Cfg → Prop} {Mentioned : Proto → Prop} {hv : HoldView}
    (h : robust_touchedFree sys Setting Mentioned hv) : no_induced_livelock_robust2 sys Setting Mentioned hv := by
  intro c₀ S hR r D hr h0 hI
  obtain ⟨i, b, n, P, _, _, ⟨-, -, hT⟩, ⟨m0, hE⟩, -, -⟩ := hI
  obtain ⟨m, hm, ht⟩ := hT m0
  exact h c₀ S hR r hr h0 m i b n P ht (hE m hm)

/-- **S5b. Mode (B), robust branch: no held-word-induced livelock**, at an arbitrary protocol list `M`. -/
theorem no_induced_livelock_robust2_thmM (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res)
    (M : List Proto) :
    no_induced_livelock_robust2 (machineE p k arch) (SettingM p k arch Init M) (· ∈ M) (hvI p k arch Init) :=
  no_induced_of_touchedFree (robust_touchedFreeM p k arch Init M)

/-- **S5a.** -/
theorem robust_touchedFree_thm (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) :
    robust_touchedFree (machineE p k arch) (Setting p k arch Init) (· ∈ protosOf p) (hvI p k arch Init) := by
  intro c₀ S
  exact robust_touchedFreeM p k arch Init (protosOf p) c₀ (settingM_of_setting S)

/-- **S5b. Mode (B), robust branch: no held-word-induced livelock** (not "no livelock"). -/
theorem no_induced_livelock_robust2_thm (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) :
    no_induced_livelock_robust2 (machineE p k arch) (Setting p k arch Init) (· ∈ protosOf p) (hvI p k arch Init) := by
  intro c₀ S
  exact no_induced_livelock_robust2_thmM p k arch Init (protosOf p) c₀ (settingM_of_setting S)

/-- **Scenario instance (S5b, S7): no held-word-induced livelock** from a scenario start with kids `kids`, for the
protocols of the program and of the kids' types (user rule). -/
theorem no_induced_livelock_robust2_scenario (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res)
    (kids : List TermSpawn.Kid) :
    no_induced_livelock_robust2 (machineE p k arch)
      (fun c0 => TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
        (fun _ => True) c0 ∧ ScenarioStartK p k arch Init kids c0)
      (· ∈ protosOf p ++ kidProtos kids) (hvI p k arch Init) := by
  intro c₀ ⟨O, hS⟩
  exact no_induced_livelock_robust2_thmM p k arch Init _ c₀ (settingM_of_scenarioK O hS)

end

end TermLiveL3
#print axioms TermLiveL3.startOKX_of_scenario
#print axioms TermLiveL3.setting_of_scenario
#print axioms TermLiveL3.setting_of_initOK
#print axioms TermLiveL3.progTyped_startW
#print axioms TermLiveL3.setting_of_startW
#print axioms TermLiveL3.scenarioStart_iff
#print axioms TermLiveL3.progTypedM_spawnS
#print axioms TermLiveL3.settingM_of_setting
#print axioms TermLiveL3.settingM_of_scenarioK
#print axioms TermLiveL3.touched_inv
#print axioms TermLiveL3.touched_inv_mem
#print axioms TermLiveL3.touched_mentionedM
#print axioms TermLiveL3.touched_mentioned
#print axioms TermLiveL3.not_heldV_of_robustPwf
#print axioms TermLiveL3.robust_touchedFreeM
#print axioms TermLiveL3.no_induced_of_touchedFree
#print axioms TermLiveL3.no_induced_livelock_robust2_thmM
#print axioms TermLiveL3.robust_touchedFree_thm
#print axioms TermLiveL3.no_induced_livelock_robust2_thm
#print axioms TermLiveL3.no_induced_livelock_robust2_scenario
#print axioms TermLiveL3.inducedW_induced
