/-
**main's flag load** (`post_step0`; the 0/1
split in `Spike/Lib/Inv2Read.lean`).

main's row at `wlBody` (an `Out.load` or `OutL.ldSt`) is the acquire load
of the flag `cT` (the word `c`'s pointer represents: `WCompat0.cw0`,
`lbl0`, `WCompat.cT`). Under the relation it reads a pre-spawn `0` or the
worker's `Tc`'s `1` (`stepOne_load_c`):

- `0`: main's source stutters at its load (`WCompat0.flagLd`), the step
  keeps memory and promises (`post_instrKeep0`);
- `1`: the flag is written (`oc = some (Tc, kc)`), and main's source takes
  its load reading `kc` (the latest source message to `cS`: `slatest_kc`),
  binding `d` to `kc`'s word of `1` (`WCompat0.rd1`); its coherence views
  only grow, so the source cover `scov0` is kept.

- `stepLoad_coh_mono`: a source load raises no coherence view.
- `src_load_latest0`: the source's load of the latest message, with the
  thread's other fields kept and its coherence raised.
- `post_flag0`: main's flag load keeps `Post`.
-/
import Spike.Lib.WakeM0Prom
import Spike.Lib.SrcMem

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.WorkerSrcStep
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1
open Spike.Lib.WakeMLive (wlRet)
open Scc.Sem.MemRel (SLatest)

/-! ## The source's load -/

/-- **A source load raises no coherence view.** -/
theorem stepLoad_coh_mono {arch : WeakMem.Arch} {mem : WeakMem.Memory} {pairs : List Nat} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : WeakMem.Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) (b : WeakMem.Address) :
    th.vs.coh b ≤ th'.vs.coh b := by
  unfold Promises.stepLoad at h
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp h
  simp only
  split
  · rename_i hb; subst hb; exact Nat.le_max_left _ _
  · exact Nat.le_refl _

/-- **The source's load of the latest message** at `let x = load acq a in
e`, the address word an untagged locative to a one-word cell: the thread
binds the message's word; memory, the paired timestamps, the promises, type
arguments, frames and thread id are kept; its coherence views only grow. -/
theorem src_load_latest0 (g : TermRun.G) (mem : WeakMem.Memory) (pairs : List Nat) (th : TermRun.TTh)
    {x : String} {acq : Bool} {a : At} {e : Expr} {ty : Ty} {pw : TermRun.Word} {μ' : Mode} {u : Ty}
    {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.load acq a) e) (hea : TermRun.evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ', u)) (hu : TermRun.accs u = some [.one])
    (hj : SLatest mem sa j) (hm : mem[j]? = some m) :
    ∃ th', (mem, pairs, th') ∈ TermRun.tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.tidLbl = th.tidLbl ∧
      ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  let s := TermRun.stOf mem pairs th
  obtain ⟨t1, ht1, hr⟩ := Scc.Sem.stepLoad_latest g.arch s.pairs (TermRun.mth s pw pw pw) 1 [0] acq hj hm
  have hl : ({ s with vs := t1.vs, undefs := s.undefs + TermRun.countUndef [⟨m.val, m.view, j⟩] },
      [⟨m.val, m.view, j⟩]) ∈ TermRun.loadUnits g.arch pw sa acq [.one] 0 s := by
    simp only [TermRun.loadUnits, SrcMem.offs_zero, List.mem_flatMap, List.mem_map]
    exact ⟨t1, ht1, _, List.mem_singleton.mpr rfl, by rw [hr]⟩
  refine ⟨⟨e, (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, t1.vs, th.promises,
    th.nalloc, th.undefs + TermRun.countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, ?mem, rfl, ?_, rfl,
    rfl, rfl, rfl, fun b => stepLoad_coh_mono ht1 b⟩
  case mem =>
    simp only [TermRun.tstep, ht, TermRun.evalOp, hea, hcell, TermRun.addrOf, hpw, hu, List.mem_map]
    exact ⟨_, ⟨_, hl, rfl⟩, by simp [s, TermRun.withS, TermRun.stOf, loadTy, hcell]⟩
  simp [loadTy, hcell]

/-! ## The flag load -/

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **main's flag load keeps `Post`**: at `wlBody`, a load of `⟨A, 8⟩` with
`A` the word `c`'s pointer represents (the row's data: `Out.load`,
`OutL.ldSt`). A pre-spawn `0` stutters; the worker's `1` is matched by the
source's load of `kc`. -/
theorem post_flag0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem)
    (hx : t.2.exited = none) (ht : s0.term = wlBody) {kl : Kraken.LoadKind} {A : BitVec 64} {g : Val → isaLSE2.State}
    (he : isaLSE2.exec t0.st = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)))
    {ty : Ty} {wd : TermRun.Word} (hev : TermRun.evalAt s0.env (.var "c") = some (ty, [wd]))
    (hv : ValRep (M.lbl w) wd.val A.toNat) :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have hpt0 := h.pt0M hPT0
  have hmi : M.Mi w t0.st (Ctl.of s0) := h.mi0 hPT0 hKR hx
  have hctl := h.mCtl hPT0
  -- the address is the flag's `cT`
  obtain ⟨cty, cμ, cu, hcv, hcell, hcu⟩ := hpt0.2.2.2.2.1
  have hwd : wd = M.cw w := by
    rw [hcv] at hev; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev
    exact hev.2.symm
  have hty : ty = cty := by
    rw [hcv] at hev; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev
    exact hev.1.symm
  subst hwd hty
  obtain ⟨a', hcT, hcTa, hcTo⟩ := hC.cT w
  have hv' := hv
  rw [hC0.cw0 w, hC0.lbl0 w] at hv'
  obtain ⟨-, x0, hx0, hA⟩ := hv'
  rw [hcTa] at hx0; cases hx0
  have hA' : A = BitVec.ofNat 64 a' := by
    apply BitVec.eq_of_toNat_eq
    have := A.isLt
    simp only [BitVec.toNat_ofNat]
    omega
  have hloc : (⟨A, 8⟩ : Loc) = (Q.C w).cT := by rw [hcT, hA']; rfl
  have heC : isaLSE2.exec t0.st = some (.load kl false (Q.C w).cT fun v => .done (g v)) := by
    rw [← hloc]; exact he
  obtain ⟨hm, hpre, v, hst, h01⟩ := stepOne_load_c Arch.armv8 h.prot h.preC heC hso ho
  obtain ⟨-, hp⟩ := stepOne_load_keep' 0 he hso ho
  obtain ⟨hne, heq⟩ := hC0.flagLd w t0.st (Ctl.of s0) kl A g ty (M.cw w) hmi ht he hev hv
  rcases h01 with rfl | ⟨Tc, kc, hoc, rfl⟩
  · -- `0`: the source stutters
    exact post_instrKeep0 hC hC0 hPT0 hKR hown h hso ho hco hm hp (.refl _)
      (hst ▸ hne 0 (by decide))
  · -- `1`: the source loads `kc`
    subst hoc
    obtain ⟨-, -, -, -, m, hmk, -, hmv⟩ := h.prot.some_msg Tc kc rfl
    have hi := h.s0_get
    obtain ⟨th', hstep, ht', he', hp', hσ', hk', htl', hcoh⟩ :=
      src_load_latest0 (TermRun.gOf wakeSrc (srcPo 2 arch wakeSrc).k (srcPo 2 arch wakeSrc).arch s 0) s.mem s.pairs s0
        (ht.trans rfl) hcv (hC0.cw0 w) hcell hcu (slatest_kc h.prot) hmk
    let w' : TermRun.Word := ⟨m.val, m.view, kc⟩
    have hmi' : M.Mi w o.thread.st (Ctl.of th') := by
      have : Ctl.of th' = ⟨wlIf, ("d", loadTy ty, [w']) :: s0.env, none⟩ := by
        simp only [Ctl.of, ht', he']; rfl
      rw [this, hst]
      exact heq 1 w' (by decide) (hC0.rd1 w w' hmv) (by rw [show w'.val = .num 1 from hmv]; exact ⟨by decide, rfl⟩)
    have hs' : ({ s with ths := s.ths.set! 0 th' } : TermRun.Cfg).ths = #[th', s1] := by
      show s.ths.set! 0 th' = _
      rw [h.ths]; rfl
    have hi' : ({ s with ths := s.ths.set! 0 th' } : TermRun.Cfg).ths[0]? = some th' := getElem?_set!_self hi th'
    have hlive : th'.term ≠ wlRet := by rw [ht']; simp [wlIf, WakeMLive.wlRet]
    have hex : SrcSem.mainExit s = [] :=
      mainExit_of_notRet h.ths hpt0.2.2.2.1 (by rw [ht]; simp [wlBody, WakeMLive.wlRet])
    have hex' : SrcSem.mainExit { s with ths := s.ths.set! 0 th' } = [] :=
      mainExit_of_notRet hs' (by rw [ht']; exact .inr (.inr (.inl rfl))) hlive
    have hrun : (wakeS arch).Run s [] { s with ths := s.ths.set! 0 th' } :=
      LRun.step (step := fun c es c' => ∃ i, (wakeS arch).step i c es c') ⟨0, WakeM0Src.source_step_nil' (P := srcPo 2 arch wakeSrc) rfl
        (.inl (.inl ⟨SrcMem.mem_threadSteps hi hstep, certified_nil hi' (by rw [hp']; exact hpt0.2.2.2.2.2.1)⟩))
        hex hex' rfl⟩ (LRun.refl _)
    have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
    have hcov := stepOne_cohL _ hso ho h.core.cov0
    rw [hm] at hb hcov
    refine ⟨_, hrun, ?_⟩
    rw [hm]
    refine post_frame0 (s := s) hC hPT0 hKR h.th hs' rfl rfl h.pt1 h.prot h.kr ?_ hpre ?_ hlive
    · refine core0_same h.core (by simp) hp hp' hb hcov
        (fun k m' hk hf => Nat.le_trans (h.core.scov0 k m' hk hf) (hcoh _)) ?_ ?_ ?_
        (fun hn => hC0.noProm0 w _ _ _ hn hco)
      · intro L v h0; simp [hown, WakeOwn.wakeOwn] at h0
      · intro L v v' h0; simp [hown, WakeOwn.wakeOwn] at h0
      · intro L v h0; simp [hown, WakeOwn.wakeOwn] at h0
    · refine ⟨.inl hmi', by rw [hk']; exact hpt0.2.1, by rw [hσ']; exact hpt0.2.2.1,
        by rw [ht']; exact .inr (.inr (.inl rfl)), ?_, by rw [hp']; exact hpt0.2.2.2.2.2.1,
        by rw [htl']; exact hpt0.2.2.2.2.2.2⟩
      rw [he']
      exact envC_cons hpt0.2.2.2.2.1 (by decide) _ _

/-- info: 'Spike.Lib.WakeM0.post_flag0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_flag0

end Spike.Lib.WakeM0
