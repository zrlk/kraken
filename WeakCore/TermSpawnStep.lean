import WeakCore.TermRun

/-! # TermSpawnStep (skeleton): the spawn configuration step

A thread at `let x = spawn f a ts in e` takes no
thread step (`tstep_spawn`: `evalOp` has `[]` for `.spawn`); its only move is `Spawn`, a
configuration step **beside** `Step` (`StepX := Step ∨ Spawn`), so no existing `Step` case split,
final or liveness statement changes meaning.

* `spawnCfg`: full barrier on the parent (`dmb sy`), the parent continues with `x := num ths.size`
  (the child's index); the child `tail f [] (var a) ts` is appended at index `ths.size`, at the
  parent's post-barrier views (`mine := []`), its argument words bumped to `vRelSt` (`bumpW`).
* `Spawn … cap`: enabled iff the parent has no promises and `ths.size < cap`.  `cap` is a parameter
  until a later revision adds the `Cfg.cap` field (then `cap := c.cap`).
* `stepsX_pres`: a predicate preserved by `Step` and by `Spawn` is preserved along `StepsX`.
* `cert_site` / `site_noProm`: at a spawn site `Certified` forces no promises; hence
  along any `StepsX` run from a promise-free start every thread at a spawn site has none, so the
  rule's `th.promises = []` never blocks a reachable spawn.
-/

namespace TermSpawnStep
open CoreLang CoreTerm TermRun TermSpawn
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The step -/

/-- (E2) The child's box: a zero-word published cell at the parent's next fresh label. -/
def tidLabel (c : Cfg) (i : Nat) (th : TTh) : AllocLabel := freshLabel c.lbase c.n i th.nalloc

/-- The parent's post-barrier state (`dmb sy`). -/
def spawnS (c : Cfg) (th : TTh) : St := fenceS (stOf c.mem c.pairs th) .sy

/-- The parent after the spawn: post-barrier, one more allocation (the child's box: machine-invisible
but for `nalloc`; its cell is ghost), continuing with `x := loc (tidLabel ..)` (the child's `ThreadId`,
a constant reference to its box). -/
def spawnPar (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr) : TTh :=
  { withS th (spawnS c th) with
    nalloc := th.nalloc + 1,
    term := e, env := (x, .tid, [cst (.loc ⟨tidLabel c i th, 0⟩ 0)]) :: th.env }

/-- The child: `tail f [] (var a) ts` on the argument words bumped to the parent's post-barrier
`vRelSt`, bound at the op's checked type `T` (A1's `kidTh` shape, `kd.ty = T`), at the parent's
post-barrier views with `mine := []`; no stack, promises or allocations. -/
def spawnKid (c : Cfg) (i : Nat) (th : TTh) (f : String) (ts : List Ty) (T : Ty) (ws : List Word) : TTh :=
  { term := .tail f [] (.var "a") ts, env := [("a", T, ws.map (TermSpawn.bumpW (spawnS c th).vs.vRelSt))],
    vs := { (spawnS c th).vs with mine := [] }, tidLbl := some (tidLabel c i th) }

/-- Replace thread `i` by `par` and append `kid`. -/
def spawnT (c : Cfg) (i : Nat) (par kid : TTh) : Cfg := { c with ths := (c.ths.set! i par).push kid }

/-- The configuration after thread `i` (`th`, at `let x = spawn f a T ts in e`, argument words `ws`) spawns. -/
def spawnCfg (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr) (f : String) (ts : List Ty)
    (T : Ty) (ws : List Word) : Cfg :=
  spawnT c i (spawnPar c i th x e) (spawnKid c i th f ts T ws)

/-- **The spawn step** of thread `i` (v2 §2).  `cap`: the thread capacity (`Cfg.cap` after M0). -/
inductive Spawn (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : Cfg → Cfg → Prop
  | mk {c : Cfg} (i : Nat) (x f : String) (a : At) (T : Ty) (ts : List Ty) (e : Expr) (th : TTh) (rt : Ty)
      (ws : List Word) :
      c.ths[i]? = some th → th.term = .let_ x (.spawn f a T ts) e → th.promises = [] →
      c.ths.size < cap → evalAt th.env a = some (rt, ws) →
      Spawn p k arch cap c (spawnCfg c i th x e f ts T ws)

/-- A machine step or a spawn. -/
def StepX (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) (c c' : Cfg) : Prop :=
  Step p k arch c c' ∨ Spawn p k arch cap c c'

/-- Runs of machine steps and steps of an arbitrary extra relation `Sp` (the old
`Steps`-based finals are the instance `Sp := ⊥`, see `StepsG.toSteps_bot`). -/
inductive StepsG (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) : Cfg → Cfg → Prop
  | refl (c : Cfg) : StepsG p k arch Sp c c
  | step {c c' c'' : Cfg} : (Step p k arch c c' ∨ Sp c c') → StepsG p k arch Sp c' c'' → StepsG p k arch Sp c c''

/-- Runs of `StepX` (= `Step ∨ Spawn`). -/
abbrev StepsX (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : Cfg → Cfg → Prop :=
  StepsG p k arch (Spawn p k arch cap)

namespace StepsG
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop}

theorem single {c c' : Cfg} (h : Step p k arch c c' ∨ Sp c c') : StepsG p k arch Sp c c' := .step h (.refl _)

theorem trans {c c' c'' : Cfg} (h : StepsG p k arch Sp c c') (h' : StepsG p k arch Sp c' c'') :
    StepsG p k arch Sp c c'' := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact .step hs (ih h')

theorem tail {c c' c'' : Cfg} (h : StepsG p k arch Sp c c') (hs : Step p k arch c' c'' ∨ Sp c' c'') :
    StepsG p k arch Sp c c'' := h.trans (single hs)

theorem ofStep {c c' : Cfg} (h : Step p k arch c c') : StepsG p k arch Sp c c' := single (.inl h)

theorem ofSp {c c' : Cfg} (h : Sp c c') : StepsG p k arch Sp c c' := single (.inr h)

-- `ofSteps` / `toSteps_bot` (against `TermStep.Steps`) live downstream of TermStep (the NoSpawn/SpawnFinal):
-- this file imports TermRun only.

/-- Monotonicity in the extra relation. -/
theorem mono {Sp' : Cfg → Cfg → Prop} (hm : ∀ c c', Sp c c' → Sp' c c') {c c' : Cfg}
    (h : StepsG p k arch Sp c c') : StepsG p k arch Sp' c c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (hs.imp id (hm _ _)) ih

end StepsG

namespace StepsX
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat}

theorem single {c c' : Cfg} (h : StepX p k arch cap c c') : StepsX p k arch cap c c' := StepsG.single h

theorem trans {c c' c'' : Cfg} (h : StepsX p k arch cap c c') (h' : StepsX p k arch cap c' c'') :
    StepsX p k arch cap c c'' := StepsG.trans h h'

theorem ofStep {c c' : Cfg} (h : Step p k arch c c') : StepsX p k arch cap c c' := StepsG.ofStep h

theorem ofSpawn {c c' : Cfg} (h : Spawn p k arch cap c c') : StepsX p k arch cap c c' := StepsG.ofSp h

end StepsX

/-- **Generic preservation**: preserved by `Step` and by `Sp` ⇒ preserved along `StepsG`. -/
theorem stepsG_pres {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {P : Cfg → Prop}
    (hS : ∀ c c', Step p k arch c c' → P c → P c') (hP : ∀ c c', Sp c c' → P c → P c')
    {c c' : Cfg} (h : StepsG p k arch Sp c c') (h0 : P c) : P c' := by
  induction h with
  | refl => exact h0
  | step hs _ ih => exact ih (hs.elim (fun h => hS _ _ h h0) (fun h => hP _ _ h h0))

/-- **Generic preservation** along `StepsX` (the instance `Sp := Spawn`). -/
theorem stepsX_pres {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {P : Cfg → Prop}
    (hS : ∀ c c', Step p k arch c c' → P c → P c') (hP : ∀ c c', Spawn p k arch cap c c' → P c → P c')
    {c c' : Cfg} (h : StepsX p k arch cap c c') (h0 : P c) : P c' := stepsG_pres hS hP h h0

/-- Elimination form of `Spawn` (for clients that need only the shape, e.g. The `viewInv_spawn`). -/
theorem Spawn.elim {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : Spawn p k arch cap c c') : ∃ i x f a T ts e th rt ws, c.ths[i]? = some th ∧
      th.term = .let_ x (.spawn f a T ts) e ∧ th.promises = [] ∧ c.ths.size < cap ∧
      evalAt th.env a = some (rt, ws) ∧ c' = spawnCfg c i th x e f ts T ws := by
  cases h with
  | mk i x f a T ts e th rt ws h1 h2 h3 h4 h5 => exact ⟨i, x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, rfl⟩

/-! ## Spawn-free programs and configurations (for `StepsX` → `Steps` reductions) -/

/-- `op` is not a spawn. -/
def opNoSpawn : Op → Bool
  | .spawn .. => false
  | _ => true

/-- No spawn anywhere in `e`. -/
def exprNoSpawn : Expr → Bool
  | .let_ _ op e => opNoSpawn op && exprNoSpawn e
  | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e | .region _ _ _ _ e | .openPub _ _ _ _ e => exprNoSpawn e
  | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂ => exprNoSpawn e₁ && exprNoSpawn e₂
  | .cas _ _ _ _ _ _ ok fail | .casp _ _ _ _ _ _ _ _ ok fail => exprNoSpawn ok && exprNoSpawn fail
  | .ret _ | .tail .. => true

/-- A spawn-free program. -/
def NoSpawnP (p : Prog) : Prop := ∀ d ∈ p, exprNoSpawn d.body = true

/-- A spawn-free configuration: every thread's term and every pending continuation. -/
def NoSpawnC (c : Cfg) : Prop :=
  ∀ th ∈ c.ths, exprNoSpawn th.term = true ∧ ∀ fr ∈ th.stack, exprNoSpawn fr.body = true

/-! ## Closed types are fixed by `close` (the arg's type transport) -/

/-- `substTs` fixes a type whose type variables are all bound below `c`. -/
theorem substTs_tb (σs : List Ty) : ∀ (t : Ty) (c d : Nat), TermClose.tb c t = true → substTs σs c d t = t := by
  intro t
  induction t with
  | tvar k => intro c d h; simp only [TermClose.tb, decide_eq_true_eq] at h; simp [substTs, h]
  | prod a b iha ihb => intro c d h; simp only [TermClose.tb, Bool.and_eq_true] at h; simp [substTs, iha c d h.1, ihb c d h.2]
  | sum a b iha ihb => intro c d h; simp only [TermClose.tb, Bool.and_eq_true] at h; simp [substTs, iha c d h.1, ihb c d h.2]
  | code a b iha ihb => intro c d h; simp only [TermClose.tb, Bool.and_eq_true] at h; simp [substTs, iha c d h.1, ihb c d h.2]
  | array i t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih c d h]
  | ptr μ t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih c d h]
  | ptrOpt μ t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih c d h]
  | loc μ t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih c d h]
  | mu t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih (c + 1) d h]
  | tex κ t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih (c + 1) d h]
  | iall t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih c (d + 1) h]
  | iex t ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih c (d + 1) h]
  | refine t ψ ih => intro c d h; simp only [TermClose.tb] at h; simp [substTs, ih c d h]
  | _ => intro c d _; rfl

/-- **`close` is the identity on `tb 0` types.** -/
theorem close_tb0 (σs : List Ty) {T : Ty} (h : TermClose.tb 0 T = true) : close σs T = T :=
  substTs_tb σs T 0 0 h

/-! ## A spawn site has no thread step -/

theorem tstep_spawn {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x f : String} {a : At}
    {T : Ty} {ts : List Ty} {e : Expr} (h : th.term = .let_ x (.spawn f a T ts) e) : tstep g mem pairs th = [] := by
  simp [tstep, h, evalOp]

theorem threadSteps_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh}
    {x f : String} {a : At} {T : Ty} {ts : List Ty} {e : Expr} (hth : c.ths[i]? = some th)
    (h : th.term = .let_ x (.spawn f a T ts) e) : threadSteps p k arch c i = [] := by
  simp [threadSteps, hth, tstep_spawn h]

/-! ## `site_noProm` -/

/-- Thread `i` of `c` sits at a spawn site. -/
def AtSite (th : TTh) : Prop := ∃ x f a T ts e, th.term = .let_ x (.spawn f a T ts) e

theorem promise_ths {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (a : Address) (v : Val) (w : Ts) :
    (promise c i a v w).ths[i]? = some { th with promises := th.promises ++ [c.mem.size] } := by
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hth
  simp only [promise, hth]
  simp [Array.set!, hi]

/-- (E1) Along `Solo i`, a thread of a kind `Q` that promising keeps and that has no thread step
and (IO1) no extern move (a spawn site) keeps its term and its promises only grow. -/
theorem solo_stuck {p : Prog} {k : Promises.Knobs} {arch : Arch} {Q : TTh → Prop}
    (hQ : ∀ th l, Q th → Q { th with promises := l })
    (hS : ∀ th, Q th → ∀ c i, c.ths[i]? = some th → threadSteps p k arch c i = [])
    (hE : ∀ th, Q th → ∀ c i, c.ths[i]? = some th → extSteps c i = [])
    {i : Nat} {c c' : Cfg} (h : Solo p k arch i c c') : ∀ th, c.ths[i]? = some th → Q th →
      ∃ th', c'.ths[i]? = some th' ∧ th.promises <+: th'.promises := by
  induction h with
  | refl c => intro th hth _; exact ⟨th, hth, List.prefix_refl _⟩
  | thread hc _ ih =>
      intro th hth hs
      rw [hS th hs _ _ hth] at hc
      cases hc
  | prom a v w _ _ ih =>
      intro th hth hs
      obtain ⟨th', h1, h2⟩ := ih _ (promise_ths hth a v w) (hQ _ _ hs)
      exact ⟨th', h1, (List.prefix_append _ _).trans h2⟩
  | ext hc _ ih =>
      intro th hth hs
      rw [hE th hs _ _ hth] at hc
      cases hc

/-- (E1) **A certified thread of such a kind has no promises.** -/
theorem cert_stuck {p : Prog} {k : Promises.Knobs} {arch : Arch} {Q : TTh → Prop}
    (hQ : ∀ th l, Q th → Q { th with promises := l })
    (hS : ∀ th, Q th → ∀ c i, c.ths[i]? = some th → threadSteps p k arch c i = [])
    (hE : ∀ th, Q th → ∀ c i, c.ths[i]? = some th → extSteps c i = [])
    {c : Cfg} {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (hs : Q th) (hc : Certified p k arch c i) : th.promises = [] := by
  obtain ⟨c', hso, hnp⟩ := hc
  obtain ⟨th', h1, h2⟩ := solo_stuck hQ hS hE hso th hth hs
  simp [noPromises, h1] at hnp
  rw [hnp] at h2
  exact List.prefix_nil.1 h2

/-- (IO1) A thread at a spawn site has no extern move. -/
theorem atSite_extSteps {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (hs : AtSite th) :
    extSteps c i = [] := by
  obtain ⟨x, f, a, T, ts, e, he⟩ := hs
  exact extSteps_nil hth (fun _ _ _ _ h => by rw [he] at h; cases h)

/-- Along `Solo i`, a thread at a spawn site keeps its term and its promises only grow. -/
theorem solo_site {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (h : Solo p k arch i c c') : ∀ th, c.ths[i]? = some th → AtSite th →
      ∃ th', c'.ths[i]? = some th' ∧ th.promises <+: th'.promises :=
  solo_stuck (Q := AtSite) (fun _ _ h => h)
    (fun _ h _ _ hth => by obtain ⟨x, f, a, T, ts, e, he⟩ := h; exact threadSteps_spawn hth he)
    (fun _ h _ _ hth => atSite_extSteps hth h) h

/-- **A certified thread at a spawn site has no promises.** -/
theorem cert_site {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (hs : AtSite th) (hc : Certified p k arch c i) : th.promises = [] :=
  cert_stuck (Q := AtSite) (fun _ _ h => h)
    (fun _ h _ _ hth => by obtain ⟨x, f, a, T, ts, e, he⟩ := h; exact threadSteps_spawn hth he)
    (fun _ h _ _ hth => atSite_extSteps hth h) hth hs hc

/-- The run invariant: every thread at a spawn site has no promises. -/
def SiteNoProm (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → AtSite th → th.promises = []

theorem threadSteps_ths_ne {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i j : Nat}
    (h : c' ∈ threadSteps p k arch c i) (hj : j ≠ i) : c'.ths[j]? = c.ths[j]? := by
  unfold threadSteps at h
  split at h
  · cases h
  · simp only [List.mem_map] at h
    obtain ⟨⟨mem, pairs, th'⟩, -, rfl⟩ := h
    simp [Array.set!, Ne.symm hj]

theorem promise_ths_ne {c : Cfg} {i j : Nat} (a : Address) (v : Val) (w : Ts) (hj : j ≠ i) :
    (promise c i a v w).ths[j]? = c.ths[j]? := by
  unfold promise
  split
  · rfl
  · simp [Array.set!, Ne.symm hj]

theorem siteNoProm_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Step p k arch c c') (h0 : SiteNoProm c) : SiteNoProm c' := by
  intro j th hth hs
  cases h with
  | thread i hc hcert =>
      by_cases hj : j = i
      · subst hj; exact cert_site hth hs hcert
      · rw [threadSteps_ths_ne hc hj] at hth; exact h0 j th hth hs
  | prom i a v w _ _ hcert =>
      by_cases hj : j = i
      · subst hj; exact cert_site hth hs hcert
      · rw [promise_ths_ne a v w hj] at hth; exact h0 j th hth hs

theorem siteNoProm_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : Spawn p k arch cap c c') (h0 : SiteNoProm c) : SiteNoProm c' := by
  intro j th' hth hs
  cases h with
  | mk i x f a T ts e th rt ws h1 _ h3 _ _ =>
      have hi : i < c.ths.size := by
        rcases Nat.lt_or_ge i c.ths.size with h | h
        · exact h
        · simp [Array.getElem?_eq_none h] at h1
      simp only [spawnCfg, spawnT, Array.getElem?_push, Array.set!, Array.getElem?_setIfInBounds] at hth
      split at hth
      · cases hth; rfl
      · split at hth
        · cases hth; simpa [spawnPar, spawnS, withS, fenceS, stOf] using h3
        · exact h0 j th' (by simpa using hth) hs

/-- **`site_noProm`**: from a start where every thread at a spawn site has no promises
(e.g. no thread has any), every reachable thread at a spawn site has none. -/
theorem site_noProm {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (hr : StepsX p k arch cap c0 c) (h0 : SiteNoProm c0) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) {x f : String} {a : At} {T : Ty} {ts : List Ty} {e : Expr}
    (he : th.term = .let_ x (.spawn f a T ts) e) : th.promises = [] :=
  have h : SiteNoProm c :=
    stepsX_pres (P := SiteNoProm) (fun _ _ h => siteNoProm_step h) (fun _ _ h => siteNoProm_spawn h) hr h0
  h i th hth ⟨x, f, a, T, ts, e, he⟩

end TermSpawnStep

#print axioms TermSpawnStep.StepsG.single
#print axioms TermSpawnStep.StepsG.trans
#print axioms TermSpawnStep.StepsG.tail
#print axioms TermSpawnStep.StepsG.ofStep
#print axioms TermSpawnStep.StepsG.ofSp
#print axioms TermSpawnStep.StepsG.mono
#print axioms TermSpawnStep.StepsX.single
#print axioms TermSpawnStep.StepsX.trans
#print axioms TermSpawnStep.StepsX.ofStep
#print axioms TermSpawnStep.StepsX.ofSpawn
#print axioms TermSpawnStep.stepsG_pres
#print axioms TermSpawnStep.stepsX_pres
#print axioms TermSpawnStep.Spawn.elim
#print axioms TermSpawnStep.substTs_tb
#print axioms TermSpawnStep.close_tb0
#print axioms TermSpawnStep.tstep_spawn
#print axioms TermSpawnStep.threadSteps_spawn
#print axioms TermSpawnStep.promise_ths
#print axioms TermSpawnStep.solo_stuck
#print axioms TermSpawnStep.cert_stuck
#print axioms TermSpawnStep.atSite_extSteps
#print axioms TermSpawnStep.solo_site
#print axioms TermSpawnStep.cert_site
#print axioms TermSpawnStep.threadSteps_ths_ne
#print axioms TermSpawnStep.promise_ths_ne
#print axioms TermSpawnStep.siteNoProm_step
#print axioms TermSpawnStep.siteNoProm_spawn
#print axioms TermSpawnStep.site_noProm
