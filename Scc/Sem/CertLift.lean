/-
**Certification across a take** (`Scc/DESIGN.md` §9.0, Decision 11): a
thread certified under the solo projection of the kernel step
(`Kernel.certSem`) at the take site stays certified after the take, under
the kernel state the take leaves (`certOkC_after_take`).

- `soloExec_congr`, `certSem_congr`: the solo projection does not depend
  on the thread's own held ranges, nor on the pool's bytes beyond their
  values (`byte`). At a transfer site `soloHeld` decides the thread's own
  entry by its private memory and keeps the others'; at a system call
  `sysStep` reads neither (and `clone`, which read the held ranges through
  `spawnStep`, has no branch).
- `certSem_take_congr`: so the take leaves the projection unchanged, given
  the pool's bytes on the taken range are zero (H1: the range was never
  released, which holds before the first release of a run).
- `certSem_step_site_out`: a certification step at a transfer site is
  deterministic: the one state the solo transfer leaves, memory unchanged.
- `certOkC_after_take_of_congr`: the lift with the congruence explicit; the
  first step of the certifying run is the take itself (P1,
  `certSem_step_of_take_self`), its tail certifies after the take.
- `certOkC_after_take`: the congruence discharged by `certSem_take_congr`.
- `take_unmapped_of_solo`, `certAfter_take`: the lift without the private
  memory premise: with promises outstanding, the certifying run's first
  step is the solo take, which succeeds only if no byte of the range is
  mapped (`soloHeld`).
-/
import Scc.Sem.CertStep

namespace Scc.Sem

open Kraken Kraken.Promising

namespace Kernel

variable {I : ISA} {K : Abi I}

/-! ## The solo projection is congruent in the thread's own ranges -/

/-- Sources with the same bytes copy the same bytes. -/
theorem copyRange_congr {src src' : _root_.Mem 64} (dst : _root_.Mem 64) (r : Range)
    (h : ∀ a, byte src a = byte src' a) : copyRange src dst r = copyRange src' dst r := by
  apply Std.ExtHashMap.ext_getElem?
  intro a
  simp only [copyRange, get_foldl_insert, h]

/-- The state of thread `tid` reads only the configuration. -/
theorem bind_stOf_congr {tid : Nat} {o o' : Option (Config I × KState)} (h : o.map (·.1) = o'.map (·.1)) :
    o.bind (stOf tid) = o'.bind (stOf tid) := by
  cases o <;> cases o' <;> simp_all [stOf]

/-- At a transfer site, the solo configuration reads the held ranges of the
others only. -/
theorem solo_site_congr {k : XferKind} {x : KState} {tid : Nat} {s : I.State} {h' : List (Nat × Range)}
    {m' : _root_.Mem 64} (hh : h'.filter (·.1 != tid) = x.held.filter (·.1 != tid)) :
    solo K (some k) { x with held := h', pmem := m' } tid s =
      ((solo K (some k) x tid s).1, { (solo K (some k) x tid s).2 with pmem := m' }) := by
  cases k <;> simp [solo, soloHeld, hh]

/-- Off the transfer sites, the solo configuration carries the held ranges
and the pool's bytes. -/
theorem solo_none_congr {x : KState} {tid : Nat} {s : I.State} {h' : List (Nat × Range)} {m' : _root_.Mem 64} :
    solo K none { x with held := h', pmem := m' } tid s =
      ((solo K none x tid s).1, { (solo K none x tid s).2 with held := h', pmem := m' }) := by
  simp [solo, soloHeld]

/-- A take leaves the same threads from pool bytes of the same values. -/
theorem takeStep_pmem_congr {tid : Nat} {c : Config I × KState} {m' : _root_.Mem 64}
    (hm : ∀ a, byte m' a = byte c.2.pmem a) :
    (takeStep K tid (c.1, { c.2 with pmem := m' })).map (·.1) = (takeStep K tid c).map (·.1) := by
  unfold takeStep
  cases c.1.threads[tid]? with
  | none => rfl
  | some t =>
    have hf : fresh (c.1, { c.2 with pmem := m' }) (siteRange K t.st) = fresh c (siteRange K t.st) := rfl
    have hr : ({ c.2 with pmem := m' } : KState).runs tid = c.2.runs tid := rfl
    simp only [hf, hr, copyRange_congr _ _ hm]
    split <;> simp_all

/-- A release leaves the same threads whatever the pool's bytes. -/
theorem releaseStep_pmem_congr {tid : Nat} {c : Config I × KState} {m' : _root_.Mem 64} :
    (releaseStep K tid (c.1, { c.2 with pmem := m' })).map (·.1) = (releaseStep K tid c).map (·.1) := by
  unfold releaseStep
  cases c.1.threads[tid]? with
  | none => rfl
  | some t =>
    have hr : ({ c.2 with pmem := m' } : KState).runs tid = c.2.runs tid := rfl
    simp only [hr]
    split <;> simp_all

/-- A transfer leaves the same threads from pool bytes of the same values. -/
theorem xferStep_pmem_congr {k : XferKind} {tid : Nat} {c : Config I × KState} {m' : _root_.Mem 64}
    (hm : ∀ a, byte m' a = byte c.2.pmem a) :
    (xferStep K k tid (c.1, { c.2 with pmem := m' })).map (·.1) = (xferStep K k tid c).map (·.1) := by
  cases k
  · exact takeStep_pmem_congr hm
  · exact releaseStep_pmem_congr

/-- A system-call step reads neither the held ranges nor the pool's bytes:
the same events and configuration. -/
theorem sysStep_held_pmem_congr {A : Arch} {tid : Nat} {c1 : Config I} {y : KState} {h' : List (Nat × Range)}
    {m' : _root_.Mem 64} {p : Pick} :
    (sysStep K A tid (c1, { y with held := h', pmem := m' }) p).map (fun q => (q.1, q.2.1)) =
      (sysStep K A tid (c1, y) p).map (fun q => (q.1, q.2.1)) := by
  unfold sysStep
  cases c1.threads[tid]? with
  | none => rfl
  | some t =>
    have hr : ready K tid (c1, { y with held := h', pmem := m' }) t = ready K tid (c1, y) t := rfl
    have hw : ({ y with held := h', pmem := m' } : KState).wr tid = y.wr tid := rfl
    simp only [hr, hw]
    split
    · rfl
    · split <;> (try simp only [back]) <;> (repeat' split) <;> simp_all [Function.comp_def]

/-- The returns `soloExec` collects at a system call read neither the held
ranges nor the pool's bytes, for any continuation `F` that reads the
events and the configuration only. -/
theorem solo_rets_congr {A : Arch} {x : KState} {tid : Nat} {s : I.State} {h' : List (Nat × Range)}
    {m' : _root_.Mem 64} {F : List Ev × (Config I × KState) → Option I.State}
    (hF : ∀ es c y y', F (es, (c, y)) = F (es, (c, y'))) (r : BitVec 64) :
    (sysStep K A tid (solo K none { x with held := h', pmem := m' } tid s) (.ret r)).bind F =
      (sysStep K A tid (solo K none x tid s) (.ret r)).bind F := by
  rw [solo_none_congr]
  generalize solo K none x tid s = q
  obtain ⟨c1, y⟩ := q
  have h := sysStep_held_pmem_congr (K := K) (A := A) (tid := tid) (c1 := c1) (y := y) (h' := h') (m' := m')
    (p := .ret r)
  revert h
  cases sysStep K A tid (c1, { y with held := h', pmem := m' }) (.ret r) <;>
    cases sysStep K A tid (c1, y) (.ret r) <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq, Option.bind_none, Option.bind_some, imp_self, false_implies]
  rename_i a b
  obtain ⟨es, c, z⟩ := a
  obtain ⟨es', c', z'⟩ := b
  intro h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hF _ _ _ _

/-- **The solo projection is congruent** in the kernel state's held ranges
of the thread itself and in the pool's bytes up to their values. -/
theorem soloExec_congr {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {s : I.State} {h' : List (Nat × Range)}
    {m' : _root_.Mem 64} (hh : h'.filter (·.1 != tid) = x.held.filter (·.1 != tid))
    (hm : ∀ a, byte m' a = byte x.pmem a) :
    soloExec K A μ { x with held := h', pmem := m' } tid s = soloExec K A μ x tid s := by
  unfold soloExec
  split
  · rename_i k _
    rw [solo_site_congr hh, bind_stOf_congr (xferStep_pmem_congr (c := solo K (some k) x tid s) hm)]
  · split
    · have hr : ∀ r : BitVec 64,
          (sysStep K A tid (solo K none { x with held := h', pmem := m' } tid s) (.ret r)).bind
              (fun q => stOf tid q.2) =
            (sysStep K A tid (solo K none x tid s) (.ret r)).bind (fun q => stOf tid q.2) :=
        fun r => solo_rets_congr (fun _ _ _ _ => rfl) r
      dsimp only
      rw [show (fun r : BitVec 64 =>
          (sysStep K A tid (solo K none { x with held := h', pmem := m' } tid s) (.ret r)).bind
            (fun q => stOf tid q.2)) =
          (fun r : BitVec 64 => (sysStep K A tid (solo K none x tid s) (.ret r)).bind
            (fun q => stOf tid q.2)) from funext hr]
    · rfl

/-- **`certSem` is congruent** as `soloExec` is. -/
theorem certSem_congr {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {h' : List (Nat × Range)}
    {m' : _root_.Mem 64} (hh : h'.filter (·.1 != tid) = x.held.filter (·.1 != tid))
    (hm : ∀ a, byte m' a = byte x.pmem a) :
    certSem K A μ { x with held := h', pmem := m' } tid = certSem K A μ x tid := by
  unfold certSem
  congr 1
  funext s
  exact soloExec_congr hh hm

/-! ## The take -/

/-- **The take's result**: thread `tid` past the `nop` with the pool's bytes
on its range, the range held by `tid` and erased from the pool's bytes;
memory unchanged. -/
theorem takeStep_eq {tid : Nat} {c c' : Config I × KState} {t : Thread I} (ht : c.1.threads[tid]? = some t)
    (h : takeStep K tid c = some c') :
    c' = (c.1.withThread tid { t with st := K.skip (K.setDmem t.st
        (copyRange c.2.pmem (K.dmem t.st) (siteRange K t.st))) } c.1.mem,
      { c.2 with held := (tid, siteRange K t.st) :: c.2.held, pmem := eraseRange c.2.pmem (siteRange K t.st) }) := by
  simp only [takeStep, ht] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- **A take leaves the projection unchanged** when the pool's bytes on the
taken range are zero (H1). -/
theorem certSem_take_congr {A : Arch} {μ : Marks} {tid : Nat} {c c' : Config I × KState} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (h : takeStep K tid c = some c')
    (hz : ∀ a ∈ addrs (siteRange K t.st), byte c.2.pmem a = 0) :
    certSem K A μ c'.2 tid = certSem K A μ c.2 tid := by
  rw [takeStep_eq ht h]
  refine certSem_congr ?_ ?_
  · simp
  · intro a
    rw [byte_eraseRange]
    split
    · rename_i ha; exact (hz a ha).symm
    · rfl

/-- **A certification step at a transfer site is deterministic**: every
outcome is the thread at the one state the solo transfer leaves, memory
unchanged (the site's instruction has no dependency). -/
theorem certSem_step_site_out {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {k : XferKind} {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}
    (hs : siteAt K μ t.st = some k) (ha : K.atSys t.st = false) (hd : I.deps t.st = {})
    (hstep : (certSem K A μ x tid).step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (xferStep K k tid (solo K (some k) x tid t.st)).bind (stOf tid) = some s' ∧
      o.thread = { t with st := s' } ∧ o.mem = mem := by
  obtain ⟨tree, st, c', hex, hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  have hex' : (certSem K A μ x tid).exec t.st =
      some (leaves ((xferStep K k tid (solo K (some k) x tid t.st)).bind (stOf tid)).toList) := by
    change soloExec K A μ x tid t.st = _
    simp only [soloExec, hs]
  rw [hex'] at hex
  cases hex
  obtain ⟨i, hi⟩ := (Lower.run_choose_iff A tid _).mp hr
  obtain ⟨rfl, rfl⟩ := (Lower.run_done_iff A tid _).mp hi
  have hdc : (certSem K A μ x tid).deps t.st = {} := by
    change certDeps K t.st = _
    rw [certDeps_of_not_atSys K ha, hd]
  rw [hdc, finishInstr_nil _ _ _ rfl] at hth
  cases hb : (xferStep K k tid (solo K (some k) x tid t.st)).bind (stOf tid) with
  | none => simp only [hb, Option.toList_none, List.length_nil] at i; exact i.elim0
  | some s' =>
    refine ⟨s', rfl, ?_, hm⟩
    rw [List.mem_singleton.mp hth]
    have key : ∀ (L : List I.State) (j : Fin L.length), L = [s'] → L[j] = s' := by
      intro L j hL; subst hL; simp
    rw [key _ i (by rw [hb]; rfl)]

/-- **Certification after a take, given the congruence**: a thread at the
take site certified under `certSem` with the kernel state before the take
(off a system call, no dependency of the site's `nop`, no byte of the range
in its private memory) is certified after the take under the kernel state
after it, if that leaves `certSem` unchanged (`hcg`). The certifying run's
first step is the take itself (P1, deterministic at the site); its tail
certifies after the take. -/
theorem certOkC_after_take_of_congr {A : Arch} {μ : Marks} {tid : Nat} {c c' : Config I × KState}
    {t : Thread I} (ht : c.1.threads[tid]? = some t) (h : takeStep K tid c = some c')
    (hs : siteAt K μ t.st = some .take) (ha : K.atSys t.st = false) (hd : I.deps t.st = {})
    (hdom : ∀ a ∈ addrs (siteRange K t.st), (K.dmem t.st)[a]? = none)
    (hcg : certSem K A μ c'.2 tid = certSem K A μ c.2 tid)
    (hc : CertOkC A (certSem K A μ c.2 tid) tid t c.1.mem) : CertAfter K A μ tid c' := by
  intro t' ht'
  rw [hcg]
  obtain ⟨outs, o, h1, h2, h3, h4⟩ := certSem_step_of_take_self (A := A) (mem := c.1.mem) ht h hs ha hd hdom
  rw [ht'] at h3
  cases h3
  have hmem : c'.1.mem = c.1.mem := by rw [takeStep_eq ht h]; rfl
  obtain ⟨s2, hb2, e2, -⟩ := certSem_step_site_out hs ha hd h1 h2
  have hprom : o.thread.prom = t.prom := by rw [e2]
  rw [hmem]
  obtain ⟨tf, mf, hrun, hp⟩ := hc
  cases hrun with
  | refl => exact certOkC_of_prom_nil (hprom.trans hp)
  | step hst hrest =>
    obtain ⟨outs2, o2, h21, h22, rfl⟩ := hst
    rw [h1] at h21
    cases h21
    obtain ⟨s1, hb1, e1, e1m⟩ := certSem_step_site_out hs ha hd h1 h22
    rw [hb1] at hb2
    cases hb2
    refine ⟨tf, mf, ?_, hp⟩
    have he : (o2.thread, o2.mem) = (o.thread, c.1.mem) := by rw [e1, e1m, e2]
    rw [he] at hrest
    exact hrest

/-- **A certification step at the take site** leaves the thread past the
`nop` with the kernel state's pool bytes on its range (the solo take),
promises and memory unchanged. -/
theorem certSem_step_take_out {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}
    (hs : siteAt K μ t.st = some .take) (ha : K.atSys t.st = false) (hd : I.deps t.st = {})
    (hstep : (certSem K A μ x tid).step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.thread = { t with st := K.skip (K.setDmem t.st (copyRange x.pmem (K.dmem t.st) (siteRange K t.st))) } ∧
      o.mem = mem := by
  obtain ⟨s', hb, ho', hm⟩ := certSem_step_site_out hs ha hd hstep ho
  refine ⟨?_, hm⟩
  rw [ho']
  obtain ⟨c'', hc'', hst⟩ := Option.bind_eq_some_iff.mp hb
  change takeStep K tid (solo K (some .take) x tid t.st) = some c'' at hc''
  cases ht : (solo K (some .take) x tid t.st).1.threads[tid]? with
  | none => simp [takeStep, ht] at hc''
  | some t0 =>
    have h0 : t0.st = t.st := solo_get ht
    have hlt := (Array.getElem?_eq_some_iff.mp ht).1
    rw [takeStep_eq ht hc''] at hst
    simp only [stOf, withThread_get, hlt, and_self, ite_true, Option.map_some, Option.some.injEq] at hst
    rw [← hst, h0]
    rfl

/-- **Certification after a take** (the lift): `certOkC_after_take_of_congr`
with the congruence discharged by `certSem_take_congr`, given the pool's
bytes on the taken range are zero (H1). -/
theorem certOkC_after_take {A : Arch} {μ : Marks} {tid : Nat} {c c' : Config I × KState} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (h : takeStep K tid c = some c')
    (hs : siteAt K μ t.st = some .take) (ha : K.atSys t.st = false) (hd : I.deps t.st = {})
    (hdom : ∀ a ∈ addrs (siteRange K t.st), (K.dmem t.st)[a]? = none)
    (hz : ∀ a ∈ addrs (siteRange K t.st), byte c.2.pmem a = 0)
    (hc : CertOkC A (certSem K A μ c.2 tid) tid t c.1.mem) : CertAfter K A μ tid c' :=
  certOkC_after_take_of_congr ht h hs ha hd hdom (certSem_take_congr ht h hz) hc

/-- **A solo take maps no byte of the range before it**: the solo
configuration holds the thread's range at a take site as soon as one byte
of it is mapped (`soloHeld`), and the range is then not fresh. -/
theorem take_unmapped_of_solo {x : KState} {tid : Nat} {s : I.State}
    (h : (takeStep K tid (solo K (some .take) x tid s)).isSome) :
    ∀ a ∈ addrs (siteRange K s), (K.dmem s)[a]? = none := by
  intro a ha
  cases hm : (K.dmem s)[a]? with
  | none => rfl
  | some b =>
    exfalso
    have hany : (addrs (siteRange K s)).any (fun a => ((K.dmem s)[a]?).isSome) = true :=
      List.any_eq_true.mpr ⟨a, ha, by simp [hm]⟩
    unfold takeStep at h
    split at h
    · simp at h
    rename_i t ht
    have hts : t.st = s := solo_get ht
    dsimp only at h
    split at h
    rotate_left
    · simp at h
    rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨-, hf⟩ := hg
    unfold fresh at hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at hf
    obtain ⟨⟨⟨⟨⟨⟨h0, -⟩, -⟩, -⟩, hh⟩, -⟩, -⟩ := hf
    have hmem : (tid, siteRange K t.st) ∈ (solo K (some .take) x tid s).2.held := by
      simp only [solo, soloHeld, hts, hany, ite_true, List.mem_cons, true_or]
    have := hh _ hmem
    simp only [overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at this
    omega

/-- **Certification after a take** with the private memory read off the
certifying run: with no promise the thread is certified after the take as
it is; otherwise the run's first step is at the take site, so the solo take
succeeds, which maps no byte of the range before it
(`take_unmapped_of_solo`), and `certOkC_after_take` applies. Given the
pool's bytes on the taken range are zero (H1). -/
theorem certAfter_take {A : Arch} {μ : Marks} {tid : Nat} {c c' : Config I × KState} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (h : takeStep K tid c = some c')
    (hs : siteAt K μ t.st = some .take) (ha : K.atSys t.st = false) (hd : I.deps t.st = {})
    (hz : ∀ a ∈ addrs (siteRange K t.st), byte c.2.pmem a = 0)
    (hc : CertOkC A (certSem K A μ c.2 tid) tid t c.1.mem) : CertAfter K A μ tid c' := by
  by_cases hp : t.prom = []
  · intro t' ht'
    refine certOkC_of_prom_nil ?_
    have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
    rw [takeStep_eq ht h] at ht'
    simp only [withThread_get, hlt, and_self, ite_true, Option.some.injEq] at ht'
    rw [← ht']; exact hp
  · obtain ⟨tf, mf, hrun, hpf⟩ := hc
    cases hrun with
    | refl => exact absurd hpf hp
    | step hst hrest =>
      obtain ⟨outs, o, hso, ho, rfl⟩ := hst
      obtain ⟨s', hb, -, -⟩ := certSem_step_site_out hs ha hd hso ho
      have hdom : ∀ a ∈ addrs (siteRange K t.st), (K.dmem t.st)[a]? = none := by
        refine take_unmapped_of_solo (x := c.2) (tid := tid) ?_
        cases hx : takeStep K tid (solo K (some .take) c.2 tid t.st) with
        | none => simp [xferStep, hx] at hb
        | some _ => rfl
      exact certOkC_after_take ht h hs ha hd hdom hz ⟨tf, mf, .step ⟨outs, o, hso, ho, rfl⟩ hrest, hpf⟩

end Kernel

end Scc.Sem
