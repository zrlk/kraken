/- **spawn-free programs keep their meaning.**
`stepsX_iff_steps_of_noSpawn : NoSpawnP p → NoSpawnC c0 → (StepsX p k arch cap c0 c ↔ TermStep.Steps p k arch c0 c)`
over the real `TermSpawnStep.StepsX`/`Spawn`/`NoSpawnP`/`NoSpawnC` and the pre-spawn `TermStep.Steps`.
Also `noSpawnC_spawnS : NoSpawnC (TermSpawn.spawnS cs res kids)` (review).
`NoS bad` is an internal Prop-level helper (bridged to the Bool `exprNoSpawn` by `noS_iff_expr`). -/
import WeakCore.TermSpawnStep
import WeakCore.TermStep
import WeakCore.TermSpawnDefs
namespace A9NoSpawn
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

variable (bad : Op → Prop)

/-- No `bad` op anywhere in `e`. -/
def NoS : Expr → Prop
  | .let_ _ op e => ¬ bad op ∧ NoS e
  | .split _ _ _ e => NoS e
  | .unpack _ _ _ e => NoS e
  | .unpackT _ _ _ e => NoS e
  | .region _ _ _ _ e => NoS e
  | .openPub _ _ _ _ e => NoS e
  | .case _ _ e₁ _ e₂ => NoS e₁ ∧ NoS e₂
  | .ifnull _ e₁ _ e₂ => NoS e₁ ∧ NoS e₂
  | .parity _ _ e₁ e₂ => NoS e₁ ∧ NoS e₂
  | .ifeq _ _ e₁ e₂ => NoS e₁ ∧ NoS e₂
  | .cas _ _ _ _ _ _ e₁ e₂ => NoS e₁ ∧ NoS e₂
  | .casp _ _ _ _ _ _ _ _ e₁ e₂ => NoS e₁ ∧ NoS e₂
  | .ret _ => True
  | .tail _ _ _ _ => True

/-- A thread's term and every frame continuation are spawn-free. -/
def ThNoS (th : TTh) : Prop := NoS bad th.term ∧ ∀ fr ∈ th.stack, NoS bad fr.body

/-- Every code block body is spawn-free. -/
def ProgNoS (p : Prog) : Prop := ∀ d ∈ p, NoS bad d.body

/-- Every thread of `c` is spawn-free. -/
def CfgNoS (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ThNoS bad th

variable {bad}

theorem enter_noS {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (hp : ProgNoS bad g.p) (hs : ∀ fr ∈ th.stack, NoS bad fr.body)
    (h : enter g th f ts a = some th') : ThNoS bad th' := by
  unfold enter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, hd, ⟨_, ws⟩, -, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  exact ⟨hp d (List.mem_of_find?_eq_some hd), hs⟩

theorem mem_optList {α : Type} {o : Option α} {r : α}
    (h : r ∈ (match o with | none => [] | some a => [a])) : o = some r := by
  cases o <;> simp_all

theorem callFrame_body {g : G} {th : TTh} {f : String} {ts : List Ty} {x : String} {e : Expr} {fr : Frame}
    (h : callFrame g th f ts x e = some fr) : fr.body = e := by
  unfold callFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, rfl⟩ := h; rfl

theorem tstep_noS {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hp : ProgNoS bad g.p) (ht : ThNoS bad th) (h : r ∈ tstep g mem pairs th) : ThNoS bad r.2.2 := by
  obtain ⟨hterm, hstk⟩ := ht
  unfold tstep at h
  split at h <;> rename_i heq <;> rw [heq] at hterm <;> simp only [NoS] at hterm
  all_goals (repeat' split at h)
  all_goals (try simp only [List.mem_nil_iff, ol, Option.toList] at h)
  all_goals (try simp only [List.mem_map, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false,
    Prod.exists] at h)
  all_goals (try (obtain ⟨_, _, _, _, rfl⟩ := h))
  all_goals (try (obtain ⟨_, _, _, rfl⟩ := h))
  all_goals (try (obtain ⟨_, _, rfl⟩ := h))
  all_goals (try (subst h))
  all_goals (try (simp only [ThNoS, withS] at hstk ⊢; first | exact ⟨hterm, hstk⟩ | exact ⟨hterm.2, hstk⟩ | exact ⟨hterm.1, hstk⟩ | done))
  · -- call
    have h1 := mem_optList h
    simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at h1
    obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := h1
    refine enter_noS hp (fun fr' hf' => ?_) hen
    rcases List.mem_cons.1 hf' with rfl | hf'
    · rw [callFrame_body hfr]; exact hterm.2
    · exact hstk fr' hf'
  · -- callc
    have h1 := mem_optList h
    simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at h1
    obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := h1
    refine enter_noS hp (fun fr' hf' => ?_) hen
    rcases List.mem_cons.1 hf' with rfl | hf'
    · show NoS bad fr.body
      rw [callFrame_body hfr]; exact hterm.2
    · exact hstk fr' hf'
  · -- case
    obtain ⟨s1, j, q, -, s2, q2, -, rfl⟩ := h
    simp only [ThNoS, withS]
    split
    · exact ⟨by simpa using hterm.1, hstk⟩
    · exact ⟨by simpa using hterm.2, hstk⟩
  · simp only [ThNoS, withS]; split <;> simp_all
  · simp only [ThNoS, withS]; split <;> simp_all
  · rename_i heqs _; simp only [ThNoS]
    exact ⟨hstk _ (by rw [heqs]; exact List.mem_cons_self), fun fr hf => hstk fr (by rw [heqs]; exact List.mem_cons_of_mem _ hf)⟩
  · have h1 := mem_optList h
    simp only [Option.map_eq_some_iff] at h1
    obtain ⟨th', hen, rfl⟩ := h1
    exact enter_noS hp hstk hen

/-! ## Port to the canonical module (TermSpawnStep) -/
open TermSpawnStep

/-- The spawn predicate for the canonical op. -/
def isSpawn (op : Op) : Prop := opNoSpawn op = false

theorem noS_iff_expr (e : Expr) : NoS isSpawn e ↔ exprNoSpawn e = true := by
  induction e with
  | let_ _ op e ih =>
      simp only [NoS, exprNoSpawn, Bool.and_eq_true, ih, isSpawn]
      cases opNoSpawn op <;> simp
  | split _ _ _ e ih | unpack _ _ _ e ih | unpackT _ _ _ e ih | region _ _ _ _ e ih
  | openPub _ _ _ _ e ih => simp only [NoS, exprNoSpawn, ih]
  | case _ _ e₁ _ e₂ ih1 ih2 | ifnull _ e₁ _ e₂ ih1 ih2 | parity _ _ e₁ e₂ ih1 ih2 | ifeq _ _ e₁ e₂ ih1 ih2
  | cas _ _ _ _ _ _ e₁ e₂ ih1 ih2 | casp _ _ _ _ _ _ _ _ e₁ e₂ ih1 ih2 =>
      simp only [NoS, exprNoSpawn, Bool.and_eq_true, ih1, ih2]
  | ret _ => simp [NoS, exprNoSpawn]
  | tail _ _ _ _ => simp [NoS, exprNoSpawn]

theorem noS_of_expr {e : Expr} (h : exprNoSpawn e = true) : NoS isSpawn e := (noS_iff_expr e).2 h
theorem expr_of_noS {e : Expr} (h : NoS isSpawn e) : exprNoSpawn e = true := (noS_iff_expr e).1 h

theorem cfgNoS_iff {c : Cfg} : NoSpawnC c ↔ CfgNoS isSpawn c := by
  constructor
  · intro h i th hth
    obtain ⟨h1, h2⟩ := h th (Array.mem_of_getElem? hth)
    exact ⟨noS_of_expr h1, fun fr hf => noS_of_expr (h2 fr hf)⟩
  · intro h th hm
    obtain ⟨i, hi⟩ := Array.getElem?_of_mem hm
    obtain ⟨h1, h2⟩ := h i th hi
    exact ⟨expr_of_noS h1, fun fr hf => expr_of_noS (h2 fr hf)⟩

theorem getElem?_set!_or {ths : Array TTh} {i j : Nat} {th' th : TTh}
    (h : (ths.set! i th')[j]? = some th) : th = th' ∨ ths[j]? = some th := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
  split at h
  · split at h
    · left; exact (Option.some.inj h).symm
    · simp at h
  · right; exact h

theorem cfgNoS_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (hp : ProgNoS isSpawn p) (hc : CfgNoS isSpawn c) (h : c' ∈ threadSteps p k arch c i) :
    CfgNoS isSpawn c' := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; cases h
  | some th =>
    rw [hth] at h
    simp only [List.mem_map] at h
    obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := h
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact tstep_noS (g := gOf p k arch c i) hp (hc i th hth) hr
    · exact hc j th0 hj

theorem cfgNoS_prom {c : Cfg} {i : Nat} {a : Address} {v : Val} {w : Ts} (hc : CfgNoS isSpawn c) :
    CfgNoS isSpawn (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact hc
  | some th =>
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact hc i th hth
    · exact hc j th0 hj

theorem cfgNoS_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (hp : ProgNoS isSpawn p) (hc : CfgNoS isSpawn c) (h : Step p k arch c c') : CfgNoS isSpawn c' := by
  cases h with
  | thread i hc' _ => exact cfgNoS_thread hp hc hc'
  | prom i a v w _ _ _ => exact cfgNoS_prom hc

/-- A spawn-free configuration has no spawn step. -/
theorem no_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (hc : CfgNoS isSpawn c) (h : Spawn p k arch cap c c') : False := by
  -- version-independent destructuring (survives the `spawn f a ts` → `spawn f a T ts`)
  cases h
  rename_i hth hterm _ _ _
  have := (hc _ _ hth).1
  rw [hterm] at this
  exact this.1 rfl

/-- (StepsR removed, copy rule) The spawn-free run relation is `StepsG p k arch (fun _ _ => False)`
(the TermSpawnStep); at assembly `StepsG.ofSteps`/`StepsG.toSteps_bot` (SpawnFinal) identify it with
`TermStep.Steps`. -/
abbrev StepsNo (p : Prog) (k : Promises.Knobs) (arch : Arch) : Cfg → Cfg → Prop :=
  StepsG p k arch (fun _ _ => False)

theorem stepsR_of_stepsX_aux {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (hp : ProgNoS isSpawn p) (h : StepsX p k arch cap c0 c) (h0 : CfgNoS isSpawn c0) :
    StepsNo p k arch c0 c ∧ CfgNoS isSpawn c := by
  induction h with
  | refl => exact ⟨.refl _, h0⟩
  | step hs _ ih =>
    rcases hs with hs | hs
    · obtain ⟨h1, h2⟩ := ih (cfgNoS_step hp h0 hs)
      exact ⟨.step (.inl hs) h1, h2⟩
    · exact (no_spawn h0 hs).elim

/-- **`stepsX_iff_steps_of_noSpawn`**: for a spawn-free program from a spawn-free start, runs with
spawns are exactly runs without, and every reachable configuration is spawn-free. -/
theorem stepsX_iff_stepsNo_of_noSpawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (hp : NoSpawnP p) (h0 : NoSpawnC c0) :
    StepsX p k arch cap c0 c ↔ StepsNo p k arch c0 c := by
  have hp' : ProgNoS isSpawn p := fun d hd => noS_of_expr (hp d hd)
  constructor
  · exact fun h => (stepsR_of_stepsX_aux hp' h (cfgNoS_iff.1 h0)).1
  · intro h
    clear h0 hp hp'
    exact StepsG.mono (fun _ _ h => h.elim) h

/-- `StepsNo` (machine steps only, as `StepsG … ⊥`) is exactly `TermStep.Steps`.
(Private bridge: the `StepsG.ofSteps`/`toSteps_bot` live in its TermStep overlay, absent on plain M0.) -/
private theorem stepsNo_iff_steps {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 c : Cfg} :
    StepsNo p k arch c0 c ↔ TermStep.Steps p k arch c0 c := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step (hs.elim id False.elim) ih
  · intro h
    induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.inl hs) ih

/-- **Spawn-free programs keep their meaning**: from a spawn-free configuration of a spawn-free
program, the `StepX` runs (machine steps or spawns) are exactly the machine-step runs `TermStep.Steps`. -/
theorem stepsX_iff_steps_of_noSpawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (hp : NoSpawnP p) (h0 : NoSpawnC c0) :
    StepsX p k arch cap c0 c ↔ TermStep.Steps p k arch c0 c :=
  (stepsX_iff_stepsNo_of_noSpawn hp h0).trans stepsNo_iff_steps

/-- Reachable configurations of a spawn-free program are spawn-free. -/
theorem noSpawnC_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (hp : NoSpawnP p) (h0 : NoSpawnC c0) (h : StepsX p k arch cap c0 c) : NoSpawnC c :=
  cfgNoS_iff.2 (stepsR_of_stepsX_aux (fun d hd => noS_of_expr (hp d hd)) h (cfgNoS_iff.1 h0)).2

/-- **Spawn-era roots are spawn-free**: the post-setup reshape `TermSpawn.spawnS cs res kids` satisfies
`NoSpawnC` unconditionally (kids start at `tail f [] (var a) ts` with no stack; if `cs` has no thread 0,
`cs.ths` is empty). -/
theorem noSpawnC_spawnS (cs : Cfg) (res : List Word) (kids : List TermSpawn.Kid) :
    NoSpawnC (TermSpawn.spawnS cs res kids) := by
  unfold TermSpawn.spawnS
  split
  · rename_i h
    intro th hm
    obtain ⟨i, hi⟩ := Array.getElem?_of_mem hm
    have h0 : cs.ths.size = 0 := by
      rcases Nat.eq_zero_or_pos cs.ths.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_getElem h'] at h
    have := (Array.getElem?_eq_some_iff.1 hi).1
    omega
  · intro th hm
    simp only [List.mem_toArray, List.mem_map] at hm
    obtain ⟨kd, -, rfl⟩ := hm
    simp [TermSpawn.kidTh, exprNoSpawn]

#print axioms enter_noS
#print axioms mem_optList
#print axioms callFrame_body
#print axioms tstep_noS
#print axioms noS_iff_expr
#print axioms noS_of_expr
#print axioms expr_of_noS
#print axioms cfgNoS_iff
#print axioms getElem?_set!_or
#print axioms cfgNoS_thread
#print axioms cfgNoS_prom
#print axioms cfgNoS_step
#print axioms no_spawn
#print axioms stepsR_of_stepsX_aux
#print axioms stepsX_iff_stepsNo_of_noSpawn
#print axioms stepsNo_iff_steps
#print axioms stepsX_iff_steps_of_noSpawn
#print axioms noSpawnC_run
#print axioms noSpawnC_spawnS
end A9NoSpawn
