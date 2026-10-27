/-
**One certification step** (`Scc/DESIGN.md` §9.0, *Certified promises in
M1*): the facts a closure proof for `StepG` (`Scc/Sem/CertProm.lean`) needs
about one `stepOneWith (Kernel.certExec K)` step, for any ISA and `Abi`.

A certification run uses `Kernel.certExec K` where the machine uses
`I.exec`. The two agree off a system call and at an unsupported one; at a
supported call `certExec` is a choice of the states `certSuccs` lists, with
no event.

- `stepOneWith_eq_of_cexec`, `stepOneWith_certExec_of_not_atSys`,
  `stepOneWith_certExec_of_decode_none`, `threadStepC_certExec_stepOne`:
  where `certExec` is the ISA's, a certification step **is** a `stepOne`,
  so the machine's instruction rows apply to it unchanged.
- `stepOneWith_runOut`: every successful outcome of `stepOneWith` is a run
  of the tree from `stepOne`'s context, finished by `finishInstr` (the
  `cexec` form of `Lower.stepOne_ok_iff`).
- `stepOneWith_bnd`: one step under any certification semantics keeps `Thread.Bnd`.
- `stepOneWith_cohP`: one step under any certification semantics keeps the cover
  `CohCoversP`.
- `stepOneWith_silent`: under any certification semantics, a step at a silent tree leaves
  memory and promises alone and lands at a leaf.
- `stepOneWith_certExec_sys`: at a supported system call, a certification
  step leaves memory and promises alone and lands in a state `certSuccs`
  lists (none for `exit`, `exit_group`: `not_stepOneWith_certExec_noRet`).
- `soloExec_cases`: `soloExec` is the ISA's `exec` or a quiet tree
  (`QuietTree`) with solo leaves (`SoloLeaf`); `soloExec_wide8CodeOn`,
  `soloExec_writeCodeOn`, `soloExec_wideInv`: so its writes and
  invariants are the ISA's; `stepOneWith_quiet`: a step at a quiet tree
  leaves memory and promises alone.
- `certSem_step_of_sysStep` (with `finishInstr_svcDeps`, `sysStep_solo`,
  `certSem_step_choose`): every return of a system call other than `clone`,
  `write`, `exit` and `exit_group` (which end a certifying run), off the
  transfer sites, is one certification step to exactly the thread the
  kernel leaves, memory unchanged.
- `certSem_step_of_take`, `certSem_step_of_take_self`,
  `certSem_step_of_release` (with `certSem_step_of_site`): a take or release
  is one certification step to exactly the thread the kernel leaves, given
  the private memory's domain on the range (none mapped at a take, all at a
  release) and no dependency of the site's instruction.
- `Inv1.of_stepOneWith`, `Inv1.silentWith`, `Inv1.certSys`: such steps keep
  the one-thread invariant.
- `msgsExcept_append`, `msgsExcept_erase`, `msgsExcept_of_eq`: the
  single-write forms of `msgsExcept_fulfil` (a store or RMW appends one
  message, or fulfils one promise; a silent step changes neither).
- `fulfil_of_msgsExcept`: the promises a step removes satisfy what
  `MsgsExcept` of the result asks (`StepG`'s fulfilment half).
- `msgsExcept_read_tlatestP`: a read of the latest write not promised is
  a value the predicate allows (the load side of `MsgsExcept`).
- `MemInv.msgsExcept`, `msgsExcept_read`, `stepOne_load_msgsExcept`:
  `MemInv G` gives `MsgsExcept`; a read of a write not promised, at any
  location, is a `G` value, as is what a load at any location reads.
-/
import Scc.Sem.CertProm
import Scc.Sem.Rows1
import Scc.Sem.SysLink

namespace Scc.Sem

open Kraken Kraken.Promising

section Step

variable {I : ISA} (A : Arch) {cs : CertSem I} {t : Thread I} {tid : Nat}
  {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}

/-- **Where `cexec` is the ISA's, `stepOneWith` is `stepOne`.** -/
theorem stepOneWith_eq_of_cexec {cexec : I.State → Option (EvTree I.State)} (h : cexec t.st = I.exec t.st) :
    stepOneWith A cexec t tid mem = stepOne A t tid mem := by
  unfold stepOneWith stepOne; rw [h]

/-- **Where the certification semantics is the ISA's (tree and
dependencies), a certification step is `stepOne`.** -/
theorem CertSem.step_eq_stepOne (he : cs.exec t.st = I.exec t.st) (hd : cs.deps t.st = I.deps t.st) :
    cs.step A t tid mem = stepOne A t tid mem := by
  unfold CertSem.step; rw [stepOneWithD_eq hd]; exact stepOneWith_eq_of_cexec A he

/-- **Every successful outcome of `stepOneWith`** is a run of the tree from
`stepOne`'s context, finished by `finishInstr`, with the memory the run
leaves. -/
theorem stepOneWith_runOut (hstep : cs.step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tree st c', cs.exec t.st = some tree ∧
      .ok (st, c') ∈ runTree A tid (instrViews t (cs.deps t.st)) (Live.TicketStep.ctx0 tid t mem) tree ∧
      o.thread ∈ finishInstr t (cs.deps t.st) (instrViews t (cs.deps t.st)) st c' ∧ o.mem = c'.mem := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      exact ⟨tree, st, c', rfl, hr, hth, rfl⟩

/-- **One step under any certification semantics keeps a thread's values at most `|M|`**
(the certification form of `stepOne_bnd`). -/
theorem stepOneWith_bnd (hstep : cs.step A t tid mem = some outs) (ho : .ok o ∈ outs)
    (ht : t.Bnd mem.last) : o.thread.Bnd o.mem.last ∧ mem.last ≤ o.mem.last := by
  obtain ⟨tree, st, c', -, hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  have hc : Ctx.Bnd (Live.TicketStep.ctx0 tid t mem) :=
    ⟨ht.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hiv := instrViews_le ht.regs (cs.deps t.st)
  obtain ⟨hc', hl⟩ := runTree_bnd A tid _ tree _ st c' hc hiv hr
  rw [hm]
  exact ⟨finishInstr_bnd hc'.views hc'.loadViews hc'.succView (hiv.mono hl) (ht.regs.mono hl) _ hth, hl⟩

/-- **One instruction under any certification semantics keeps the cover** (the `cexec` form
of `stepOne_cohP`). -/
theorem stepOneWith_cohP (hstep : cs.step A t tid mem = some outs) (ho : .ok o ∈ outs)
    (hc : CohCoversP t.views t.prom mem) : CohCoversP o.thread.views o.thread.prom o.mem := by
  obtain ⟨tree, st, c', -, hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  have hc' := runTree_cohP A tid _ tree _ st c' hr hc
  obtain ⟨e1, e2⟩ := finishInstr_relKey hth
  have e3 : o.thread.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
  intro k w hk hp
  rw [e1] at hp
  rw [hm] at hk
  have := hc' k w hk hp
  unfold Views.getCoh at this ⊢
  rw [e3]; exact this

/-- **A step at a silent tree, under any certification semantics**: memory and promises
unchanged, the thread at a leaf. -/
theorem stepOneWith_silent {tree : EvTree I.State} {P : I.State → Prop} (hex : cs.exec t.st = some tree)
    (hs : Lower.SilentTree P tree) (hstep : cs.step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t.prom ∧ P o.thread.st := by
  obtain ⟨tree', st, c', hex', hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  rw [hex] at hex'; cases hex'
  obtain ⟨s, hP, he⟩ := hs.run A tid _ hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hm, (finishInstr_relKey hth).1, (finishInstr_st hth) ▸ hP⟩

end Step

/-! ## Certification steps of the canonical targets -/

namespace Kernel

variable {I : ISA} {K : Abi I} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}

/-- At a system call that does not decode, the certification semantics is
the ISA's. -/
theorem certExec_of_decode_none {s : I.State} (h : decode K.nrs (K.nr s) (K.arg s) = none) :
    certExec K s = I.exec s := by
  unfold certExec; split <;> simp [h]

/-- **Off a system call, a certification step is a `stepOne`.** -/
theorem stepOneWith_certExec_of_not_atSys (h : K.atSys t.st = false) :
    stepOneWith A (certExec K) t tid mem = stepOne A t tid mem :=
  stepOneWith_eq_of_cexec A (certExec_of_not_atSys K h)

/-- **At a system call that does not decode, a certification step is a
`stepOne`.** -/
theorem stepOneWith_certExec_of_decode_none (h : decode K.nrs (K.nr t.st) (K.arg t.st) = none) :
    stepOneWith A (certExec K) t tid mem = stepOne A t tid mem :=
  stepOneWith_eq_of_cexec A (certExec_of_decode_none h)

/-- **A certification step from a state that is not a supported system call
is a machine instruction step** (`stepOne`), with the same outcome. -/
theorem threadStepC_certExec_stepOne {x y : Thread I × Memory} (hs : ThreadStepC A (certExec K) tid x y)
    (h : K.atSys x.1.st = false ∨ decode K.nrs (K.nr x.1.st) (K.arg x.1.st) = none) :
    ∃ outs o, stepOne A x.1 tid x.2 = some outs ∧ .ok o ∈ outs ∧ y = (o.thread, o.mem) := by
  obtain ⟨outs, o, hso, ho, rfl⟩ := hs
  have he : stepOneWith A (certExec K) x.1 tid x.2 = stepOne A x.1 tid x.2 := by
    rcases h with h | h
    · exact stepOneWith_certExec_of_not_atSys A h
    · exact stepOneWith_certExec_of_decode_none A h
  exact ⟨outs, o, he ▸ hso, ho, rfl⟩

/-- **A certification step at a supported system call** leaves memory and
promises alone, and the thread resumes in a state `certSuccs` lists. -/
theorem stepOneWith_certExec_sys {call : Call} (hs : K.atSys t.st = true)
    (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = some call)
    (hstep : stepOneWith A (certExec K) t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t.prom ∧ o.thread.st ∈ certSuccs K t.st call := by
  obtain ⟨tree, st, c', hex, hr, hth, hm⟩ := stepOneWith_runOut (cs := CertSem.ofExec (certExec K)) A hstep ho
  change certExec K t.st = some tree at hex
  rw [certExec_of_decode hs hd] at hex
  cases hex
  obtain ⟨i, hi⟩ := (Lower.run_choose_iff A tid _).mp hr
  simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at hi
  obtain ⟨rfl, rfl⟩ := hi
  exact ⟨hm, (finishInstr_relKey hth).1, (finishInstr_st hth) ▸ List.getElem_mem _⟩

/-- **A certification run stops at `exit` and `exit_group`**: no successful
step there. -/
theorem not_stepOneWith_certExec_noRet {call : Call} (hs : K.atSys t.st = true)
    (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = some call) (hc : call = .exit ∨ ∃ v, call = .exitGroup v)
    (hstep : stepOneWith A (certExec K) t tid mem = some outs) : ¬ .ok o ∈ outs := by
  intro ho
  have h := (stepOneWith_certExec_sys A hs hd hstep ho).2.2
  rcases hc with rfl | ⟨v, rfl⟩ <;> simp [certSuccs, results] at h

end Kernel

/-! ## The shape of the solo projection

`soloExec` is the ISA's `exec`, or a quiet tree (choices and plain loads,
no write) whose leaves are the thread's state, past a transfer site, or
returned from a call (`soloExec_cases`). So it writes as the ISA's `exec`
does (`soloExec_wide8CodeOn`, `soloExec_writeCodeOn`), keeps what `exec`
keeps and the solo leaves keep (`soloExec_wideInv`), and a step at a quiet
tree keeps memory and promises (`stepOneWith_quiet`). -/

namespace Kernel

variable {I : ISA} {K : Abi I}

/-- The state of thread `tid` after replacing it. -/
theorem stOf_withThread_self {c : Config I} {tid : Nat} {th : Thread I} {mem : Memory} {x : KState}
    {s' : I.State} (h : stOf tid ((c.withThread tid th mem), x) = some s') : s' = th.st := by
  simp only [stOf, withThread_get] at h
  split at h
  · cases h; rfl
  · simp_all

/-- **A range transfer leaves the thread past the site** with some private
memory (`skip ∘ setDmem`). -/
theorem xferStep_st {k : XferKind} {tid : Nat} {c c' : Config I × KState} {s' : I.State}
    (h : xferStep K k tid c = some c') (h' : stOf tid c' = some s') :
    ∃ t, c.1.threads[tid]? = some t ∧ ∃ m, s' = K.skip (K.setDmem t.st m) := by
  cases k <;> simp only [xferStep, takeStep, releaseStep] at h <;> split at h <;> try cases h
  all_goals
    rename_i t ht
    split at h
    · cases h; exact ⟨t, ht, _, stOf_withThread_self h'⟩
    · cases h

/-- **A system-call step returning `r` leaves the thread** where it was (no
return), at `ret r`, or at `ret r` after `setTp`. -/
theorem sysStep_st {A : Arch} {tid : Nat} {c c' : Config I × KState} {r : BitVec 64} {es : List Ev}
    {s' : I.State} (h : sysStep K A tid c (.ret r) = some (es, c')) (h' : stOf tid c' = some s') :
    ∃ t, c.1.threads[tid]? = some t ∧
      (s' = t.st ∨ s' = K.ret t.st r ∨ ∃ a, s' = K.ret (K.setTp t.st a) r) := by
  unfold sysStep at h
  split at h
  · cases h
  rename_i t ht
  refine ⟨t, ht, ?_⟩
  have hb : ∀ (u : Thread I) (x : KState) (es' : List Ev), back K tid c u r x es' = some (es, c') →
      s' = K.ret u.st r := by
    intro u x es' hb
    simp only [back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact (stOf_withThread_self h').trans (retThread_st _ _)
  have hs : c'.1 = c.1 → s' = t.st := by
    intro he
    simp only [stOf, he, ht, Option.map_some, Option.some.injEq] at h'
    exact h'.symm
  split at h
  · cases h
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> simp only [hcall] at h <;> (repeat' split at h) <;> (try cases h)
  all_goals first
    | exact .inr (.inl ((stOf_withThread_self h').trans (retThread_st _ _)))
    | exact .inr (.inr ⟨_, (stOf_withThread_self h').trans (retThread_st _ _)⟩)
    | exact .inl (hs rfl)
    | skip

/-- **A `clone` leaves the parent at `ret ctid`**, with its private memory
changed if it hands the child a range. -/
theorem spawnStep_st {tid j : Nat} {c c' : Config I × KState} {ctid : BitVec 64} {s' : I.State}
    (h : spawnStep K tid c j ctid = some c') (h' : stOf tid c' = some s') :
    ∃ t, c.1.threads[tid]? = some t ∧ (s' = K.ret t.st ctid ∨ ∃ m, s' = K.ret (K.setDmem t.st m) ctid) := by
  unfold spawnStep at h
  split at h
  · cases h
  rename_i t ht
  refine ⟨t, ht, ?_⟩
  split at h
  · cases h
  rename_i hrd
  split at h
  · split at h
    · rename_i hcond
      obtain ⟨hdor, -, -, -⟩ := hcond
      have hjt : j ≠ tid := by
        rintro rfl
        simp [ready, KState.runs, hdor] at hrd
      have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
      split at h
      · cases h
        simp only [stOf, withThread_get, hjt, false_and, ite_false, hlt, and_self, ite_true, Option.map_some,
          Option.some.injEq] at h'
        exact .inl (h'.symm.trans (retThread_st _ _))
      · cases h
        simp only [stOf, withThread_get, hjt, false_and, ite_false, hlt, and_self, ite_true, Option.map_some,
          Option.some.injEq] at h'
        exact .inr ⟨_, h'.symm.trans (retThread_st _ _)⟩
    · cases h
  · cases h

/-- The thread `tid` of the solo configuration. -/
theorem solo_get {site : Option XferKind} {x : KState} {tid : Nat} {s : I.State} {t : Thread I}
    (h : (solo K site x tid s).1.threads[tid]? = some t) : t.st = s := by
  simp only [solo, Array.getElem?_replicate] at h
  split at h
  · cases h; rfl
  · cases h

/-- A tree of choices and loads only, no write. -/
def QuietTree {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, QuietTree (k i)
  | .load _ _ _ ret => ∀ v, QuietTree (ret v)
  | _ => False

/-- The states a leaf of `soloExec` off the ISA's `exec` may be. The last
disjunct (a return after a change of private memory) was `clone` handing
its child a stack range; `soloExec` no longer has a leaf at `clone`,
but the disjunct is kept so the users' case splits stand. -/
def SoloLeaf (K : Abi I) (s s' : I.State) : Prop :=
  s' = s ∨ (∃ m, s' = K.skip (K.setDmem s m)) ∨ (∃ r, s' = K.ret s r) ∨ (∃ a r, s' = K.ret (K.setTp s a) r) ∨
    ∃ m r, s' = K.ret (K.setDmem s m) r

/-- A choice of `done`s is quiet. -/
theorem leaves_quiet (L : List I.State) : QuietTree (leaves L) := fun _ => trivial

/-- The leaves of `leaves L` are in `L`. -/
theorem leaves_leaf {L : List I.State} {s' : I.State} (h : TreeLeaf (leaves L) s') : s' ∈ L := by
  obtain ⟨i, hi⟩ := h
  exact hi ▸ List.getElem_mem _

/-- The returns of `sysStep` from the solo configuration are solo leaves. -/
theorem rets_leaf {A : Arch} {x : KState} {tid : Nat} {s s' : I.State} {rs : List (BitVec 64)}
    (h : s' ∈ rs.filterMap fun r => (sysStep K A tid (solo K none x tid s) (.ret r)).bind fun (_, c') => stOf tid c') :
    SoloLeaf K s s' := by
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.mp h
  obtain ⟨⟨es, c'⟩, hs, hc'⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨t, ht, h⟩ := sysStep_st hs hc'
  rw [solo_get ht] at h
  rcases h with h | h | ⟨a, h⟩
  · exact .inl h
  · exact .inr (.inr (.inl ⟨r, h⟩))
  · exact .inr (.inr (.inr (.inl ⟨a, r, h⟩)))

/-- **The trees of `soloExec`**: the ISA's `exec`, or a tree of choices and
loads whose leaves are the thread's state, past a transfer site
(`skip ∘ setDmem`), or returned from a call (`ret`, possibly after
`setTp`; `clone` has no leaf). -/
theorem soloExec_cases {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {s : I.State} {tree : EvTree I.State}
    (h : soloExec K A μ x tid s = some tree) :
    I.exec s = some tree ∨ (QuietTree tree ∧ ∀ s', TreeLeaf tree s' → SoloLeaf K s s') := by
  unfold soloExec at h
  split at h
  · cases h
    refine .inr ⟨leaves_quiet _, fun s' hl => ?_⟩
    have hm := leaves_leaf hl
    rw [Option.mem_toList, Option.bind_eq_some_iff] at hm
    obtain ⟨c', hx, hc'⟩ := hm
    obtain ⟨t, ht, m, rfl⟩ := xferStep_st hx hc'
    rw [solo_get ht]
    exact .inr (.inl ⟨m, rfl⟩)
  · split at h
    · split at h
      · cases h
        exact .inr ⟨leaves_quiet _, fun s' hl => absurd (leaves_leaf hl) List.not_mem_nil⟩
      · cases h
        exact .inr ⟨leaves_quiet _, fun s' hl => absurd (leaves_leaf hl) List.not_mem_nil⟩
      · cases h
        exact .inr ⟨leaves_quiet _, fun s' hl => rets_leaf (leaves_leaf hl)⟩
      · exact .inl h
    · exact .inl h

/-- A quiet tree writes nothing, so as any `G` says. -/
theorem QuietTree.writeTree {σ : Type} {G : Loc → Val → Prop} : ∀ {t : EvTree σ}, QuietTree t → WriteTree G t
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => QuietTree.writeTree (h i)
  | .load _ _ _ _, h => fun v => QuietTree.writeTree (h v)
  | .store _ _ _ _ _, h => h.elim
  | .rmw _ _ _ _ _, h => h.elim
  | .fence _ _, h => h.elim

/-- A quiet tree writes words only. -/
theorem QuietTree.wide8 {σ : Type} : ∀ {t : EvTree σ}, QuietTree t → Wide8Tree t
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => QuietTree.wide8 (h i)
  | .load _ _ _ _, h => fun v => QuietTree.wide8 (h v)
  | .store _ _ _ _ _, h => h.elim
  | .rmw _ _ _ _ _, h => h.elim
  | .fence _ _, h => h.elim

/-- **A run of a quiet tree** keeps memory and promises. -/
theorem QuietTree.run (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} :
    ∀ {t : EvTree σ}, QuietTree t → ∀ {c : Ctx} {s : σ} {c' : Ctx}, .ok (s, c') ∈ runTree A tid iv c t →
      c'.mem = c.mem ∧ c'.prom = c.prom
  | .done _, _, c, s, c', hx => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx; exact ⟨rfl, rfl⟩
  | .fault _, _, _, _, _, hx => by simp [runTree] at hx
  | .choose _ k, h, c, s, c', hx => by
    obtain ⟨i, hi⟩ := (Lower.run_choose_iff A tid iv).mp hx
    exact QuietTree.run A tid iv (h i) hi
  | .load _ _ _ ret, h, c, s, c', hx => by
    simp only [runTree, List.mem_flatMap] at hx
    obtain ⟨⟨tm, v, c1⟩, h1, h2⟩ := hx
    obtain ⟨-, -, -, he⟩ := readSuccs_shape A iv h1
    have := QuietTree.run A tid iv (h v) h2
    simp only at he
    rw [this.1, this.2, he]
    exact ⟨rfl, rfl⟩
  | .store _ _ _ _ _, h, _, _, _, _ => h.elim
  | .rmw _ _ _ _ _, h, _, _, _, _ => h.elim
  | .fence _ _, h, _, _, _, _ => h.elim

/-- **A certification step at a quiet tree** keeps memory and promises; the
thread is at a leaf. -/
theorem stepOneWith_quiet {A : Arch} {cs : CertSem I} {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}
    {tree : EvTree I.State} (hex : cs.exec t.st = some tree) (hq : QuietTree tree)
    (hstep : cs.step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t.prom ∧ TreeLeaf tree o.thread.st := by
  obtain ⟨tree', st, c', hex', hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  rw [hex] at hex'; cases hex'
  obtain ⟨h1, h2⟩ := hq.run A tid _ hr
  exact ⟨hm.trans h1, (finishInstr_relKey hth).1.trans h2,
    (finishInstr_st hth) ▸ runTree_treeLeaf A tid _ tree _ st c' hr⟩

section Shape

variable {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {P : I.State → Prop}

/-- `soloExec` writes words only where the ISA's `exec` does. -/
theorem soloExec_wide8CodeOn (h : Wide8CodeOn P I.exec) : Wide8CodeOn P (soloExec K A μ x tid) :=
  fun _ _ hs he => (soloExec_cases he).elim (h _ _ hs) (·.1.wide8)

/-- `soloExec` writes as `G` says where the ISA's `exec` does. -/
theorem soloExec_writeCodeOn {G : Loc → Val → Prop} (h : WriteCodeOn G P I.exec) :
    WriteCodeOn G P (soloExec K A μ x tid) :=
  fun _ _ hs he => (soloExec_cases he).elim (h _ _ hs) (·.1.writeTree)

/-- **An invariant of the ISA's `exec` closed under the solo leaves is an
invariant of `soloExec`.** -/
theorem soloExec_wideInv (h : WideInv P I.exec) (hl : ∀ s s', P s → SoloLeaf K s s' → P s') :
    WideInv P (soloExec K A μ x tid) :=
  fun _ _ _ hs he hleaf => (soloExec_cases he).elim (fun he => h _ _ _ hs he hleaf) (fun h => hl _ _ hs (h.2 _ hleaf))

end Shape

/-- The write record of the calling thread in the solo configuration is 0. -/
theorem solo_wr {site : Option XferKind} {x : KState} {tid : Nat} {s : I.State} (h : tid < x.slots.size) :
    (solo K site x tid s).2.wr tid = 0 := by
  simp [solo, KState.wr, h]

/-- **The returns of a call other than `clone` from the solo configuration
are branches of `certExec`** (`certSuccs`), by `sysStep_ret_mem`: the solo
configuration has no byte of a `write` out. -/
theorem rets_certSuccs {A : Arch} {x : KState} {tid : Nat} {s s' : I.State} {call : Call} {rs : List (BitVec 64)}
    (hd : decode K.nrs (K.nr s) (K.arg s) = some call)
    (h : s' ∈ rs.filterMap fun r => (sysStep K A tid (solo K none x tid s) (.ret r)).bind fun (_, c') => stOf tid c')
    (hx : call ≠ .exit) (hg : ∀ v, call ≠ .exitGroup v) : s' ∈ certSuccs K s call := by
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.mp h
  obtain ⟨⟨es, c'⟩, hs, hc'⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨t, ht, -⟩ := sysStep_st hs hc'
  have hts := solo_get ht
  have hlt : tid < x.slots.size := by
    have := (Array.getElem?_eq_some_iff.mp ht).1
    simpa [solo] using this
  have hc : callOf K t = some call := by rw [callOf, hts]; exact hd
  obtain ⟨t', ht', hm⟩ := sysStep_ret_mem ht hc hs (fun _ _ _ _ => by rw [solo_wr hlt]; omega) hx hg
  simp only [stOf, ht', Option.map_some, Option.some.injEq] at hc'
  rw [← hc', ← hts]; exact hm

/-- **At a supported system call other than `clone`, off the transfer
sites, the solo projection is a quiet tree whose leaves are branches of
`certExec`** (`certSuccs`): the returns `sysStep` gives the solo
configuration (none at `write`, which ends a certifying run). -/
theorem soloExec_sys {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {s : I.State} {call : Call}
    {tree : EvTree I.State} (hs : siteAt K μ s = none) (ha : K.atSys s = true)
    (hd : decode K.nrs (K.nr s) (K.arg s) = some call) (hcl : ∀ st tl, call ≠ .clone st tl)
    (h : soloExec K A μ x tid s = some tree) :
    QuietTree tree ∧ ∀ s', TreeLeaf tree s' → s' ∈ certSuccs K s call := by
  have hex : ∀ {s'}, s' ∈ (results call).filterMap (fun r => (sysStep K A tid (solo K none x tid s) (.ret r)).bind
      fun (_, c') => stOf tid c') → s' ∈ certSuccs K s call := by
    intro s' hm
    by_cases hx : call = .exit
    · subst hx; simp [results] at hm
    by_cases hg : ∃ v, call = .exitGroup v
    · obtain ⟨v, rfl⟩ := hg; simp [results] at hm
    exact rets_certSuccs hd hm hx fun v hv => hg ⟨v, hv⟩
  simp only [soloExec, hs, ha, ite_true, hd] at h
  split at h
  · rename_i st tl he; cases he; exact absurd rfl (hcl st tl)
  · cases h
    exact ⟨leaves_quiet _, fun s' hl => absurd (leaves_leaf hl) List.not_mem_nil⟩
  · rename_i call' hne he
    cases h
    cases he
    exact ⟨leaves_quiet _, fun s' hl => hex (leaves_leaf hl)⟩
  · rename_i he; cases he

/-- **A certification step at a supported system call other than `clone`,
off the transfer sites**, keeps memory and promises, and resumes the thread
in a state `certSuccs` lists. -/
theorem certSem_step_sys {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I} {call : Call}
    (hs : siteAt K μ t.st = none) (ha : K.atSys t.st = true)
    (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = some call) (hcl : ∀ st tl, call ≠ .clone st tl)
    (hstep : (certSem K A μ x tid).step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t.prom ∧ o.thread.st ∈ certSuccs K t.st call := by
  obtain ⟨tree, -, -, hex, -⟩ := stepOneWith_runOut A hstep ho
  obtain ⟨hq, hl⟩ := soloExec_sys hs ha hd hcl hex
  obtain ⟨hm, hp, hleaf⟩ := stepOneWith_quiet hex hq hstep ho
  exact ⟨hm, hp, hl _ hleaf⟩

/-- **Off the transfer sites**: no site of the marks is at the pc. -/
theorem siteAt_eq_none_iff {μ : Marks} {s : I.State} :
    siteAt K μ s = none ↔ μ.site .take ≠ some (K.pc s) ∧ μ.site .release ≠ some (K.pc s) := by
  unfold siteAt
  by_cases h1 : μ.site .take = some (K.pc s) <;> by_cases h2 : μ.site .release = some (K.pc s) <;> simp [h1, h2]

/-- A state `certSuccs` lists is a solo leaf (`ret`, after `setTp` at
`arch_prctl`). -/
theorem certSuccs_soloLeaf {s s' : I.State} {call : Call} (h : s' ∈ certSuccs K s call) : SoloLeaf K s s' := by
  cases call <;> simp only [certSuccs, List.mem_map, List.mem_singleton] at h
  case archSetFs a => exact .inr (.inr (.inr (.inl ⟨a, 0, h⟩)))
  all_goals obtain ⟨r, -, rfl⟩ := h; exact .inr (.inr (.inl ⟨r, rfl⟩))

/-- **Off the transfer sites and system calls, a certification step is
`stepOne`.** -/
theorem certSem_step_of_not_site {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    (hs : siteAt K μ t.st = none) (ha : K.atSys t.st = false) :
    (certSem K A μ x tid).step A t tid mem = stepOne A t tid mem :=
  CertSem.step_eq_stepOne A (soloExec_of_not_atSys K hs ha) (certDeps_of_not_atSys K ha)

/-! ### The kernel's returns are certification steps

A step of `sysStep` returning `r` to thread `tid` from a call other than
`clone`, `write`, `exit` and `exit_group` is matched
by a certification step (`certSem_step_of_sysStep`): the solo configuration
returns the same `r` to the same state (`sysStep_solo`), so that state is a
branch of `soloExec`, and finishing the instruction under the kernel's
dependencies (`finishInstr_svcDeps`) gives exactly the thread `retThread`
leaves, with memory unchanged. A `write` has no certification step
(`soloExec` has no branch there), so it is excluded too. -/

/-- **The kernel's dependencies give no input view**: finishing an
instruction under `svcDeps` sets the result registers' views to 0, as
`retThread` does. -/
theorem finishInstr_svcDeps (t : Thread I) (st : I.State) (c : Ctx) :
    finishInstr t (svcDeps K) (instrViews t (svcDeps K)) st c =
      [K.retRegs.foldl (fun t reg => t.setRegView reg 0 0) { t with st, views := c.views, prom := c.prom }] := by
  simp [finishInstr, svcDeps, instrViews, Thread.joinViews]

/-- **The solo configuration returns what the real one returns**: a return
of `r` to a thread with no byte of a `write` out is also a return of `r`
from the solo configuration of that thread's state, to the same state. -/
theorem sysStep_solo {A : Arch} {tid : Nat} {c c' : Config I × KState} {r : BitVec 64} {es : List Ev}
    {t : Thread I} {x : KState} (ht : c.1.threads[tid]? = some t) (h : sysStep K A tid c (.ret r) = some (es, c'))
    (hw : c.2.wr tid = 0) (hlt : tid < x.slots.size) :
    ∃ es' c'', sysStep K A tid (solo K none x tid t.st) (.ret r) = some (es', c'') ∧
      stOf tid c'' = stOf tid c' := by
  have hsl : (solo K none x tid t.st).1.threads[tid]? = some (Thread.init t.st) := by
    simp [solo, hlt]
  have hlt' : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  have hrd : ready K tid (solo K none x tid t.st) (Thread.init t.st) = K.atSys t.st := by
    simp [ready, solo, KState.runs, hlt, Thread.init]
  have hwr : (solo K none x tid t.st).2.wr tid = 0 := solo_wr hlt
  have hco : callOf K (Thread.init t.st) = callOf K t := rfl
  unfold sysStep at h ⊢
  rw [ht] at h
  rw [hsl]
  simp only at h ⊢
  split at h
  · cases h
  rename_i hr
  rw [hrd]
  have hat : K.atSys t.st = true := by simp [ready] at hr; exact hr.1.1
  simp only [hat, Bool.not_true, Bool.false_eq_true, ite_false, hco, hwr, hw] at h ⊢
  have hls : tid < (solo K none x tid t.st).1.threads.size := by simp [solo, hlt]
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> simp only [hcall] at h ⊢ <;> (repeat' split at h) <;> (try cases h)
  all_goals simp only [*, back, Option.some.injEq, ite_true, ite_false]
  all_goals exact ⟨_, _, rfl, by
    first
      | simp only [stOf, ht, hsl, Option.map_some]; rfl
      | simp [stOf, withThread_get, hls, hlt', Thread.init]⟩

/-- **A certification step at a choice** reaches, from a `done` branch, each
thread `finishInstr` gives, with memory unchanged. -/
theorem certSem_step_choose {A : Arch} {cs : CertSem I} {t : Thread I} {tid : Nat} {mem : Memory} {n : Nat}
    {k : Fin n → EvTree I.State} {s : I.State} (hex : cs.exec t.st = some (.choose n k)) (i : Fin n)
    (hk : k i = .done s) {th : Thread I}
    (hth : th ∈ finishInstr t (cs.deps t.st) (instrViews t (cs.deps t.st)) s
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }) :
    ∃ outs o, cs.step A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread = th ∧ o.mem = mem := by
  let ctx : Ctx := { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }
  have hr : Except.ok (s, ctx) ∈ runTree A tid (instrViews t (cs.deps t.st)) ctx (.choose n k) :=
    (Lower.run_choose_iff A tid _).mpr ⟨i, by rw [hk]; simp [runTree]⟩
  refine ⟨_, { thread := th, mem, promisedNow := [], log := [.instr tid (I.showInstr t.st)] },
    by unfold CertSem.step stepOneWithD; rw [hex]; rfl, List.mem_flatMap.mpr ⟨_, hr, ?_⟩, rfl, rfl⟩
  exact List.mem_map.mpr ⟨th, hth, rfl⟩

/-- **Every return of a system call is a certification step** (P1): a
`sysStep` returning `r` to thread `tid` at a call other than `clone`,
`write`, `exit` and `exit_group` (each of which ends a certifying run), off
the transfer sites, leaves the thread exactly as one certification step
under `certSem` with any kernel state `x` (with `tid` a slot of `x`) does,
memory unchanged. -/
theorem certSem_step_of_sysStep {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {c c' : Config I × KState}
    {r : BitVec 64} {es : List Ev} {t : Thread I} {mem : Memory} {call : Call}
    (ht : c.1.threads[tid]? = some t) (hc : callOf K t = some call) (h : sysStep K A tid c (.ret r) = some (es, c'))
    (hw : c.2.wr tid = 0) (hlt : tid < x.slots.size) (hs : siteAt K μ t.st = none)
    (hcl : ∀ st tl, call ≠ .clone st tl) (hnw : ∀ fd buf n, call ≠ .write fd buf n) (hx : call ≠ .exit)
    (hg : ∀ v, call ≠ .exitGroup v) :
    ∃ outs o, (certSem K A μ x tid).step A t tid mem = some outs ∧ .ok o ∈ outs ∧
      c'.1.threads[tid]? = some o.thread ∧ o.mem = mem := by
  obtain ⟨hr, s0, ht', hs0⟩ := sysStep_ret_shape ht hc h (fun _ _ _ _ => by rw [hw]; omega) hx hg
  obtain ⟨es', c'', hso, hst⟩ := sysStep_solo (x := x) ht h hw hlt
  have hat : K.atSys t.st = true := by
    unfold sysStep at h; rw [ht] at h; simp only at h
    split at h
    · cases h
    · rename_i hrd; simp [ready] at hrd; exact hrd.1.1
  have hst' : stOf tid c'' = some (K.ret s0 r) := by rw [hst]; simp [stOf, ht']
  have hmem : K.ret s0 r ∈ (results call).filterMap fun r =>
      (sysStep K A tid (solo K none x tid t.st) (.ret r)).bind fun (_, c') => stOf tid c' :=
    List.mem_filterMap.mpr ⟨r, hr, by rw [hso]; exact hst'⟩
  have hd : certDeps K t.st = svcDeps K := by simp [certDeps, hat]
  have hth : retThread K { t with st := s0 } r ∈ finishInstr t ((certSem K A μ x tid).deps t.st)
      (instrViews t ((certSem K A μ x tid).deps t.st)) (K.ret s0 r)
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } := by
    change _ ∈ finishInstr t (certDeps K t.st) (instrViews t (certDeps K t.st)) _ _
    rw [hd, finishInstr_svcDeps]
    exact List.mem_singleton.mpr rfl
  have hdc : decode K.nrs (K.nr t.st) (K.arg t.st) = some call := hc
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hmem
  rw [ht']
  have hgen : (∀ fd buf n, call ≠ .write fd buf n) → (certSem K A μ x tid).exec t.st = some (leaves
      ((results call).filterMap fun r =>
        (sysStep K A tid (solo K none x tid t.st) (.ret r)).bind fun (_, c') => stOf tid c')) := by
    intro hnw
    change soloExec K A μ x tid t.st = _
    simp only [soloExec, hs, hat, ite_true, hdc]
  cases call with
  | write fd buf n => exact absurd rfl (hnw fd buf n)
  | clone st tl => exact absurd rfl (hcl st tl)
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | _ =>
    obtain ⟨outs, o, h1, h2, h3, h4⟩ := certSem_step_choose (A := A) (mem := mem) (hgen (by simp)) ⟨j, hj⟩
      (congrArg EvTree.done hjs) hth
    exact ⟨outs, o, h1, h2, by rw [h3], h4⟩


/-! ### Range transfers are certification steps

A take or release of thread `tid` at its site is matched by a certification
step to exactly the thread the kernel leaves (`certSem_step_of_take`,
`certSem_step_of_release`), given the private memory decides the site as
`soloHeld` reads it (at a take no byte of the range is mapped, at a release
every byte is: what the fragment's invariant `OwnDom` gives), and the
site's `nop` has no dependency (`A64.deps_of_atNop`, `X64.deps_of_atNop`). -/

/-- Finishing an instruction with no dependencies leaves the thread's
registers' views as they were. -/
theorem finishInstr_nil (t : Thread I) (st : I.State) (c : Ctx) (hl : c.loadViews = []) :
    finishInstr t {} (instrViews t {}) st c = [{ t with st, views := c.views, prom := c.prom }] := by
  simp [finishInstr, hl]

/-- **A step at a transfer site is a certification step**, given the solo
transfer leaves the thread at `s'` and the site's instruction has no
dependencies. -/
theorem certSem_step_of_site {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {k : XferKind} {c'' : Config I × KState} {s' : I.State} (hs : siteAt K μ t.st = some k)
    (ha : K.atSys t.st = false) (hd : I.deps t.st = {})
    (hx : xferStep K k tid (solo K (some k) x tid t.st) = some c'') (hst : stOf tid c'' = some s') :
    ∃ outs o, (certSem K A μ x tid).step A t tid mem = some outs ∧ .ok o ∈ outs ∧
      o.thread = { t with st := s' } ∧ o.mem = mem := by
  have hex : (certSem K A μ x tid).exec t.st = some (leaves [s']) := by
    change soloExec K A μ x tid t.st = _
    simp only [soloExec, hs, hx, Option.bind_some, hst, Option.toList_some]
  have hdc : (certSem K A μ x tid).deps t.st = {} := by
    change certDeps K t.st = _
    rw [certDeps_of_not_atSys K ha, hd]
  refine certSem_step_choose (A := A) (mem := mem) hex ⟨0, by simp⟩ rfl ?_
  rw [hdc, finishInstr_nil _ _ _ rfl]
  exact List.mem_singleton.mpr rfl

/-- The state of thread `tid` after replacing it, when it is a slot. -/
theorem stOf_withThread {c : Config I} {tid : Nat} {th : Thread I} {mem : Memory} {x : KState}
    (h : tid < c.threads.size) : stOf tid ((c.withThread tid th mem), x) = some th.st := by
  simp [stOf, withThread_get, h]

/-- **Every release is a certification step** (P1): a `releaseStep` of
thread `tid`, off a system call, at the release site of the marks, with every
byte of the range mapped in the thread's private memory and no dependency of
the site's instruction, leaves the thread exactly as one certification step
does, memory unchanged. -/
theorem certSem_step_of_release {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {c c' : Config I × KState}
    {t : Thread I} {mem : Memory} (ht : c.1.threads[tid]? = some t) (h : releaseStep K tid c = some c')
    (hlt : tid < x.slots.size) (hs : siteAt K μ t.st = some .release) (ha : K.atSys t.st = false)
    (hd : I.deps t.st = {}) (hdom : ∀ a ∈ addrs (siteRange K t.st), ((K.dmem t.st)[a]?).isSome) :
    ∃ outs o, (certSem K A μ x tid).step A t tid mem = some outs ∧ .ok o ∈ outs ∧
      c'.1.threads[tid]? = some o.thread ∧ o.mem = mem := by
  have hlt' : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  simp only [releaseStep, ht] at h
  split at h
  · rename_i hg
    cases h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨⟨⟨⟨-, -⟩, hn⟩, -⟩, hon⟩ := hg
    have hsl : (solo K (some .release) x tid t.st).1.threads[tid]? = some (Thread.init t.st) := by
      simp [solo, hlt]
    have hls : tid < (solo K (some .release) x tid t.st).1.threads.size := by simp [solo, hlt]
    obtain ⟨y, hrel⟩ : ∃ y, releaseStep K tid (solo K (some .release) x tid t.st) = some
        ((solo K (some .release) x tid t.st).1.withThread tid
          { Thread.init t.st with st := K.skip (K.setDmem t.st (eraseRange (K.dmem t.st) (siteRange K t.st))) }
          (solo K (some .release) x tid t.st).1.mem, y) := by
      simp only [releaseStep, hsl]
      split
      · exact ⟨_, rfl⟩
      rename_i hne
      refine absurd ?_ hne
      have hall : (addrs (siteRange K t.st)).all (fun a => ((K.dmem t.st)[a]?).isSome) = true :=
        List.all_eq_true.mpr hdom
      simp only [solo, soloHeld, hall, ite_true]
      simp [KState.runs, hlt, Thread.init, hn, hon]
    obtain ⟨outs, o, h1, h2, h3, h4⟩ := certSem_step_of_site (A := A) (mem := mem) hs ha hd hrel
      (stOf_withThread hls)
    refine ⟨outs, o, h1, h2, ?_, h4⟩
    rw [h3]; simp [withThread_get, hlt']
  · cases h

/-- **Every take is a certification step** (P1): a `takeStep` of thread
`tid`, off a system call, at the take site of the marks, with no byte of the
range mapped in the thread's private memory, no dependency of the site's
instruction, and the solo kernel state `x` agreeing with the real one on the
pool, the others' held ranges and the pool's bytes on the range, leaves the
thread exactly as one certification step does, memory unchanged. -/
theorem certSem_step_of_take {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {c c' : Config I × KState}
    {t : Thread I} {mem : Memory} (ht : c.1.threads[tid]? = some t) (h : takeStep K tid c = some c')
    (hlt : tid < x.slots.size) (hs : siteAt K μ t.st = some .take) (ha : K.atSys t.st = false)
    (hd : I.deps t.st = {}) (hdom : ∀ a ∈ addrs (siteRange K t.st), (K.dmem t.st)[a]? = none)
    (hpool : x.pool = c.2.pool) (hheld : ∀ h ∈ x.held, h.1 ≠ tid → h ∈ c.2.held)
    (hpm : copyRange x.pmem (K.dmem t.st) (siteRange K t.st) = copyRange c.2.pmem (K.dmem t.st) (siteRange K t.st)) :
    ∃ outs o, (certSem K A μ x tid).step A t tid mem = some outs ∧ .ok o ∈ outs ∧
      c'.1.threads[tid]? = some o.thread ∧ o.mem = mem := by
  have hlt' : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  simp only [takeStep, ht] at h
  split at h
  · rename_i hg
    cases h
    simp only [Bool.and_eq_true] at hg
    obtain ⟨⟨⟨-, -⟩, hn⟩, hf⟩ := hg
    have hsl : (solo K (some .take) x tid t.st).1.threads[tid]? = some (Thread.init t.st) := by
      simp [solo, hlt]
    have hls : tid < (solo K (some .take) x tid t.st).1.threads.size := by simp [solo, hlt]
    have hany : (addrs (siteRange K t.st)).any (fun a => ((K.dmem t.st)[a]?).isSome) = false := by
      simp only [List.any_eq_false]; intro a ha; simp [hdom a ha]
    have hf' : fresh (solo K (some .take) x tid t.st) (siteRange K t.st) = true := by
      simp only [fresh, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf ⊢
      obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := hf
      refine ⟨⟨⟨⟨⟨⟨h0, ?_⟩, ?_⟩, h3⟩, ?_⟩, ?_⟩, ?_⟩
      · simpa [solo, hpool] using h1
      · simpa [solo, hpool] using h2
      · intro hh hm
        simp only [solo, soloHeld, hany, Bool.false_eq_true, ite_false, List.mem_filter, bne_iff_ne,
          ne_eq] at hm
        exact h4 hh (hheld hh hm.1 hm.2)
      · simp [solo]
      · simp [solo]
    obtain ⟨y, htk⟩ : ∃ y, takeStep K tid (solo K (some .take) x tid t.st) = some
        ((solo K (some .take) x tid t.st).1.withThread tid
          { Thread.init t.st with st := K.skip (K.setDmem t.st (copyRange x.pmem (K.dmem t.st) (siteRange K t.st))) }
          (solo K (some .take) x tid t.st).1.mem, y) := by
      simp only [takeStep, hsl]
      split
      · exact ⟨_, rfl⟩
      rename_i hne
      refine absurd ?_ hne
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, hn⟩, hf'⟩ <;> simp [solo, KState.runs, hlt]
    obtain ⟨outs, o, h1, h2, h3, h4⟩ := certSem_step_of_site (A := A) (mem := mem) hs ha hd htk
      (stOf_withThread hls)
    refine ⟨outs, o, h1, h2, ?_, h4⟩
    rw [h3]; simp [withThread_get, hlt', hpm]
  · cases h

/-- A running thread's id is a slot. -/
theorem lt_of_runs {x : KState} {tid : Nat} (h : x.runs tid = true) : tid < x.slots.size := by
  unfold KState.runs at h
  split at h
  · rename_i hs; exact (Array.getElem?_eq_some_iff.mp hs).1
  · cases h

/-- **`certSem_step_of_take` at the kernel state of the step.** -/
theorem certSem_step_of_take_self {A : Arch} {μ : Marks} {tid : Nat} {c c' : Config I × KState}
    {t : Thread I} {mem : Memory} (ht : c.1.threads[tid]? = some t) (h : takeStep K tid c = some c')
    (hs : siteAt K μ t.st = some .take) (ha : K.atSys t.st = false) (hd : I.deps t.st = {})
    (hdom : ∀ a ∈ addrs (siteRange K t.st), (K.dmem t.st)[a]? = none) :
    ∃ outs o, (certSem K A μ c.2 tid).step A t tid mem = some outs ∧ .ok o ∈ outs ∧
      c'.1.threads[tid]? = some o.thread ∧ o.mem = mem := by
  have hr : c.2.runs tid = true := by
    simp only [takeStep, ht] at h
    split at h
    · rename_i hg; simp only [Bool.and_eq_true] at hg; exact hg.1.1.1
    · cases h
  exact certSem_step_of_take ht h (lt_of_runs hr) hs ha hd hdom rfl (fun h hm _ => hm) rfl

end Kernel

/-! ## The one-thread invariant along certification steps -/

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory} {A : Arch}
  {cs : CertSem I} {tid : Nat}
  {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}

/-- **A step under any certification semantics that keeps memory and promises keeps
`Inv1`** (the certification form of the `stepOne` cover argument). -/
theorem of_stepOneWith (h : Inv1 Λ lbl lsize ts t tm sm) (hstep : cs.step A t tid tm = some outs)
    (ho : .ok o ∈ outs) (hm : o.mem = tm) (hp : o.thread.prom = t.prom) : Inv1 Λ lbl lsize ts o.thread o.mem sm :=
  ⟨by rw [hm, hp]; exact h.mem, stepOneWith_cohP A hstep ho h.coh, hm ▸ h.narrow⟩

/-- **A silent step under any certification semantics**: memory and promises unchanged, the
thread at a leaf, `Inv1` kept. -/
theorem silentWith (h : Inv1 Λ lbl lsize ts t tm sm) {tree : EvTree I.State} {P : I.State → Prop}
    (hex : cs.exec t.st = some tree) (hs : Lower.SilentTree P tree)
    (hstep : cs.step A t tid tm = some outs) (ho : .ok o ∈ outs) :
    o.mem = tm ∧ o.thread.prom = t.prom ∧ P o.thread.st ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨hm, hp, hP⟩ := stepOneWith_silent A hex hs hstep ho
  exact ⟨hm, hp, hP, h.of_stepOneWith hstep ho hm hp⟩

/-- **A certification step at a supported system call**: memory and
promises unchanged, the thread in a state `certSuccs` lists, `Inv1`
kept. -/
theorem certSys (h : Inv1 Λ lbl lsize ts t tm sm) {K : Kernel.Abi I} {call : Kernel.Call}
    (hs : K.atSys t.st = true) (hd : Kernel.decode K.nrs (K.nr t.st) (K.arg t.st) = some call)
    (hstep : stepOneWith A (Kernel.certExec K) t tid tm = some outs) (ho : .ok o ∈ outs) :
    o.mem = tm ∧ o.thread.prom = t.prom ∧ o.thread.st ∈ Kernel.certSuccs K t.st call ∧
      Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨hm, hp, hc⟩ := Kernel.stepOneWith_certExec_sys A hs hd hstep ho
  exact ⟨hm, hp, hc, h.of_stepOneWith (cs := CertSem.ofExec (Kernel.certExec K)) hstep ho hm hp⟩

/-- **A certification step of the solo projection at a supported system
call other than `clone`, off the transfer sites**: memory and promises
unchanged, the thread in a state `certSuccs` lists, `Inv1` kept. -/
theorem certSysSolo (h : Inv1 Λ lbl lsize ts t tm sm) {K : Kernel.Abi I} {call : Kernel.Call} {μ : Marks}
    {x : Kernel.KState} (hsi : Kernel.siteAt K μ t.st = none) (hs : K.atSys t.st = true)
    (hd : Kernel.decode K.nrs (K.nr t.st) (K.arg t.st) = some call) (hcl : ∀ st tl, call ≠ .clone st tl)
    (hstep : (Kernel.certSem K A μ x tid).step A t tid tm = some outs) (ho : .ok o ∈ outs) :
    o.mem = tm ∧ o.thread.prom = t.prom ∧ o.thread.st ∈ Kernel.certSuccs K t.st call ∧
      Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨hm, hp, hc⟩ := Kernel.certSem_step_sys hsi hs hd hcl hstep ho
  exact ⟨hm, hp, hc, h.of_stepOneWith hstep ho hm hp⟩

end Inv1

/-! ## `MsgsExcept` under one write -/

section MsgsExcept

variable {Pm : Msg → Prop} {prom : List Time} {mem : Memory}

/-- Memory and promises unchanged keep `MsgsExcept`. -/
theorem msgsExcept_of_eq {prom' : List Time} {mem' : Memory} (h : MsgsExcept Pm prom mem) (hm : mem' = mem)
    (hp : prom' = prom) : MsgsExcept Pm prom' mem' := by
  subst hm hp; exact h

/-- **An appended message satisfying `Pm`, the promises unchanged** (a
store or RMW that does not fulfil), keeps `MsgsExcept`. -/
theorem msgsExcept_append (h : MsgsExcept Pm prom mem) {w : Msg} (hw : Pm w) :
    MsgsExcept Pm prom (mem.append w).1 := by
  intro k m hk hn
  by_cases he : k = mem.last + 1
  · subst he; rw [Memory.get?_append_new] at hk; cases hk; exact hw
  · exact h k m (CohCoversP.get?_append_ne hk he) hn

/-- **A fulfilled promise of a message satisfying `Pm`, memory unchanged**
(a store or RMW that fulfils `q`), keeps `MsgsExcept`. -/
theorem msgsExcept_erase (h : MsgsExcept Pm prom mem) {q : Time} {w : Msg} (hq : mem.get? q = some w)
    (hw : Pm w) : MsgsExcept Pm (prom.erase q) mem := by
  intro k m hk hn
  by_cases he : k = q
  · subst he; rw [hq] at hk; cases hk; exact hw
  · exact h k m hk fun hp => hn ((List.mem_erase_of_ne he).mpr hp)

/-- **The promises a step removes are messages `MsgsExcept` covers after
it**: a step under any certification semantics only appends to memory, so a removed promise's
message is still there, and it is no longer exempt. With `Pm` the property
`StepG` asks of fulfilments, `MsgsExcept Pm` of the result gives `StepG`'s
second half. -/
theorem fulfil_of_msgsExcept {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}
    {x y : Thread I × Memory} (hs : ThreadStepC A cs tid x y) (h : MsgsExcept Pm y.1.prom y.2) :
    ∀ p ∈ x.1.prom, p ∉ y.1.prom → ∀ w, x.2.get? p = some w → Pm w := by
  intro p _ hpy w hg
  obtain ⟨outs, o, hso, ho, rfl⟩ := hs
  exact h p w (by rw [(stepOneWith_prefix A hso ho).get? (Memory.le_last_of_get? hg)]; exact hg) hpy

/-- **A read of the latest write not promised is a `G` value** when every
initial value and every message but the promised ones is: what a load
reads under the cover (`stepOne_load_tlatestP`), so `MemInv G` with its
messages stated as `MsgsExcept` serves for loads. -/
theorem msgsExcept_read_tlatestP {G : Loc → Val → Prop} (h : MsgsExcept (fun m => G m.loc m.val) prom mem)
    (hi : ∀ l, G l (mem.initVal l)) {a ts : Nat} {v : Val} (hl : TLatestP mem prom a ts)
    (hr : mem.read? (wordLoc a) ts = some v) : G (wordLoc a) v := by
  unfold Memory.read? at hr
  split at hr
  · cases hr; exact hi _
  · rename_i h0
    split at hr
    · rename_i w hw
      split at hr
      · rename_i hb
        cases hr
        have hb : w.loc = wordLoc a := by simpa using hb
        rcases hl.1 with h0' | ⟨-, -, -, hn⟩
        · exact absurd h0' h0
        · exact hb ▸ h ts w hw hn
      · cases hr
    · cases hr

/-- **`MemInv G` gives `MsgsExcept` for any promises** (every message is a
`G` value). -/
theorem MemInv.msgsExcept {G : Loc → Val → Prop} (h : MemInv G mem) (prom : List Time) :
    MsgsExcept (fun m => G m.loc m.val) prom mem := by
  refine MsgsExcept.of_all (fun k m hk => ?_) prom
  unfold Memory.get? at hk
  split at hk
  · cases hk
  · exact h.2 m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))

/-- **A read of a write not promised is a `G` value**, at any location,
when every initial value and every message but the promised ones is. -/
theorem msgsExcept_read {G : Loc → Val → Prop} (h : MsgsExcept (fun m => G m.loc m.val) prom mem)
    (hi : ∀ l, G l (mem.initVal l)) {l : Loc} {ts : Nat} {v : Val} (hr : mem.read? l ts = some v)
    (hn : ts ∉ prom) : G l v := by
  unfold Memory.read? at hr
  split at hr
  · cases hr; exact hi _
  · split at hr
    · rename_i w hw
      split at hr
      · rename_i hb
        cases hr
        have hb : w.loc = l := by simpa using hb
        exact hb ▸ h ts w hw hn
      · cases hr
    · cases hr

/-- **A load at any location reads a `G` value** when every initial value
and every message but the thread's promised ones is: Kraken's `read` rule
reads no promised write. -/
theorem stepOne_load_msgsExcept {I : ISA} {A : Arch} {G : Loc → Val → Prop} {t : Thread I} {tid : Nat}
    {kl : LoadKind} {xcl : Bool} {L : Loc} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl L fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (h : MsgsExcept (fun m => G m.loc m.val) t.prom mem)
    (hi : ∀ l, G l (mem.initVal l)) : ∃ v, o.thread.st = g v ∧ G L v := by
  obtain ⟨st, c', hr, hth, -⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts, v, hx, rfl⟩ := hr
  obtain ⟨ts', v', he, -, hv, -, hp⟩ := (mem_readSuccs A).mp hx
  cases he
  refine ⟨v, finishInstr_st hth, msgsExcept_read h hi hv fun hm => ?_⟩
  have : t.prom.contains ts = true := List.elem_eq_true_of_mem hm
  exact absurd this (by simpa using hp)

end MsgsExcept

end Scc.Sem
