/-
**Stage 3, O2–O5: promise-free liveness of the x64
ticket lock with an unlocked release under weak fairness and memory
fairness** (`ticket2_x64_live_pf`), for `ticketlock2.kl`'s worker verbatim,
on a valid layout of its image `tk2ImageV`, under `Arch.tso`. An adapted copy
of `LiveX64TicketPF.lean` (ticketlock3); the argument is unchanged except at
the release.

On a promise-free stuttering trace from a start configuration,
`LiveX64Ticket2Inv.trace_inv` gives `InvW` at every index. Write `m` for the
value of `owner` (`Mo`).

- `m` never decreases, and while it stays, so does the last write to `owner`
  (`M_step`); a thread holding a ticket keeps it (`tk_persist`).
- Suppose thread `T` waits with ticket `K` and never leaves positions 0–6.
  Then `m ≤ K` forever, so `m` is eventually constant, from `n` on
  (`SpinCommon.evconst`). The holder `H` of `m` exists (`tkSurj`).
- `H` sits at one of the positions 4–10 forever (11 and 13 need a ticket
  `< m`), so it is always instruction-enabled (`henH`; the release by
  `Ticket2X64Step.en_ldst`) and, by weak fairness, scheduled infinitely often.
- Its release `incl (owner)` reads `m` — its coherence view of `owner` is at
  the last write (`CInv`, from its spin read of `m` and `uniq`) — and writes
  `m + 1`, which would raise `m`, so it never gets through the critical
  section (`cs_false`); so it spins forever and reads `owner` infinitely
  often (`reads_inf`). Memory fairness brings its view of `owner` up to the
  (fixed) last write; its next spin iteration enters the critical section
  (`at_false`): contradiction.

`MemFair` on x86 is a modelling assumption (finite store-buffer drain, as in
x86-TSO; see `LiveTrace.lean`).

**Invalid layouts.** The theorem assumes `ValidLayout (layout tk2ImageV)`, as
the safety theorem `ticket2_counter_envG_verbatim` does.
-/
import Kraken.Promising.LiveX64Ticket2Inv
import Kraken.Promising.LiveSpinCommon
import Kraken.Promising.LiveTkHolderP
import Kraken.Promising.SLR.EnvG.X64Ticket2Runner

namespace Kraken.Promising.Live.Ticket2X64PF

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.Ticket2X64Trees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.Ticket2X64Inv Kraken.Promising.Live.SpinCommon Kraken.Promising.Live.Ticket2X64Step
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV symTk2 StartStateTk2)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk2ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk2ImageV).addrOf

/-- A thread holding a ticket keeps it across an instruction step. -/
theorem step_tk {N xc m tid j : Nat} {cfg cfg' : Config isa} {t : Thread isa}
    (h : InvW N xc m cfg) (hi : InstrBy Arch.tso tid cfg cfg') (ht : cfg.threads[j]? = some t)
    (hk : Ticketed t) : ∃ t', cfg'.threads[j]? = some t' ∧ Ticketed t' ∧ tk t' = tk t := by
  obtain ⟨u, outs, oc, hu, hs, ho, rfl⟩ := hi
  by_cases e : j = tid
  · subst e; rw [ht] at hu; cases hu
    have hxc : xc + 1 < 2 ^ 32 := by have := h.xcN; have := h.N32; omega
    cases thread_step (h.thr j t ht) hxc h.mxc h.fx h.fo h.hxo (fun _ _ _ _ _ => hk) h.ov h.uniq hs ho with
    | same _ _ htk hk' => exact ⟨_, wt_tid ht, htk.mpr hk, hk' hk⟩
    | tkt _ _ _ _ h0 => exact absurd hk h0
    | rel _ _ _ _ _ h1 hk0 hk' => exact ⟨_, wt_tid ht, h1, hk'.trans hk0.symm⟩
  · exact ⟨t, by rw [wt_ne hu e]; exact ht, hk, rfl⟩

/-- The value of `owner` at index `i`. -/
abbrev Mo {fuel : Nat} (tr : TraceS Arch.tso fuel isa) (i : Nat) : Nat :=
  ((tr.cfg i).mem.finalVal OL).toNat

section Trace

variable {fuel N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceS Arch.tso fuel isa}
  (hs : Ticket2X64.Tk2StartX N states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
  (hpf : PromiseFree Arch.tso tr.cfg)

include hs h0 hpf

theorem inv_at (i : Nat) : ∃ xc, InvW N xc (Mo tr i) (tr.cfg i) := by
  obtain ⟨xc, m, h⟩ := trace_inv hs tr h0 hpf i
  have := h.fo; subst this; exact ⟨xc, h⟩

theorem M_step (i : Nat) : (Mo tr (i + 1) = Mo tr i ∧
    (tr.cfg (i + 1)).mem.lastWrite OL = (tr.cfg i).mem.lastWrite OL) ∨ Mo tr (i + 1) = Mo tr i + 1 := by
  rcases step_or hpf i with he | ⟨tid, hi, hm⟩
  · simp only [Mo]; rw [he]; exact .inl ⟨rfl, rfl⟩
  obtain ⟨xc, h⟩ := inv_at hs h0 hpf i
  rcases step_inv h (h.bnd.succ hm) hi with ⟨xc', h', hl⟩ | h'
  · exact .inl ⟨h'.fo, hl⟩
  · exact .inr h'.fo

theorem M_mono (i j : Nat) (hij : i ≤ j) : Mo tr i ≤ Mo tr j := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step k _ ih => show _ ≤ Mo tr (k + 1); rcases M_step hs h0 hpf k with ⟨e, -⟩ | e <;> omega

theorem tk_persist {tid i : Nat} {t : Thread isa} (ht : (tr.cfg i).threads[tid]? = some t) (hk : Ticketed t) :
    ∀ j, i ≤ j → ∃ t', (tr.cfg j).threads[tid]? = some t' ∧ Ticketed t' ∧ tk t' = tk t := by
  intro j hj
  induction hj with
  | refl => exact ⟨t, ht, hk, rfl⟩
  | @step k _ ih =>
    obtain ⟨t', h1, h2, h3⟩ := ih
    rcases step_or hpf k with he | ⟨tid', hi, -⟩
    · rw [he]; exact ⟨t', h1, h2, h3⟩
    · obtain ⟨xc, h⟩ := inv_at hs h0 hpf k
      obtain ⟨u, hu1, hu2, hu3⟩ := step_tk h hi h1 h2
      exact ⟨u, hu1, hu2, hu3.trans h3⟩

/-! ## The holder of a constant `owner` -/

section Holder

variable {n m H : Nat} (hM : ∀ j, n ≤ j → Mo tr j = m)
  (hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite OL = (tr.cfg n).mem.lastWrite OL)
  (hH : ∀ j, n ≤ j → ∃ t, (tr.cfg j).threads[H]? = some t ∧ Ticketed t ∧ tk t = m)
  (hwf : WeakFairInstr Arch.tso fuel tr.cfg)

include hM hL hH hwf

theorem hold (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t) :
    TInv m ((tr.cfg j).mem.lastWrite OL) t ∧ tk t = m ∧ (tr.cfg j).Bnd ∧
      ∃ p ∈ [4, 5, 6, 7, 8, 9, 10], t.st.st.2 = pcA p ∧ PcInv m t.st.st.1 p := by
  obtain ⟨xc, h⟩ := inv_at hs h0 hpf j
  rw [hM j hj] at h
  obtain ⟨t', h1, h2, h3⟩ := hH j hj
  rw [ht] at h1; cases h1
  have hT := h.thr H t ht
  refine ⟨hT, h3, h.bnd, ?_⟩
  obtain ⟨i, hi, hpc, hinv, -⟩ := hT.pc
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  unfold tk at h3
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpc h2.1
  · exact absurd hpc h2.2
  all_goals first | exact ⟨_, by decide, hpc, hinv⟩ | (simp only [PcInv] at hinv; omega)

theorem henH (j : Nat) (hj : n ≤ j) : InstrEnabled Arch.tso fuel H (tr.cfg j) := by
  obtain ⟨t, ht, -⟩ := hH j hj
  obtain ⟨hT, -, hb, p, hp, hpc, -⟩ := hold hs h0 hpf hM hL hH hwf _ hj ht
  have hS := hT.st
  have hb' := hb H t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g, -, hex⟩ := exec_ldo _ (hS.at (by decide) (by decide) hpc) hS.dO
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso H hT.prom hex (mem := (tr.cfg j).mem)
    exact instrEnabled_of Arch.tso H ht h1 h2 h3
  · obtain ⟨md, -, -, -, -, hex⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
    obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso H hex (mem := (tr.cfg j).mem)
    exact instrEnabled_of Arch.tso H ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso H (exec_jne _ (hS.at (by decide) (by decide) hpc))
       (mem := (tr.cfg j).mem)
    exact instrEnabled_of Arch.tso H ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨g, -, hex⟩ := exec_ldc _ (hS.at (by decide) (by decide) hpc) hS.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso H hT.prom hex (mem := (tr.cfg j).mem)
    exact instrEnabled_of Arch.tso H ht h1 h2 h3
  · obtain ⟨md, -, -, -, hex⟩ := exec_addd _ (hS.at (by decide) (by decide) hpc)
    obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso H hex (mem := (tr.cfg j).mem)
    exact instrEnabled_of Arch.tso H ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨v, md, -, -, -, hex⟩ := exec_stc _ (hS.at (by decide) (by decide) hpc) hS.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso H hT.prom hb' hex
    exact instrEnabled_of Arch.tso H ht h1 h2 h3
  · obtain ⟨g, -, hex⟩ := exec_inc _ (hS.at (by decide) (by decide) hpc) hS.dO
    obtain ⟨_, _, h1, h2, h3⟩ := en_ldst Arch.tso H hT.prom hb' hex
    exact instrEnabled_of Arch.tso H ht h1 h2 h3

/-- **`H`'s next step** (weak fairness; `SpinCommon.adv`). -/
theorem advH (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t) :
    ∃ k, j ≤ k ∧ (tr.cfg k).threads[H]? = some t ∧ ∃ outs oc, stepOne Arch.tso t H (tr.cfg k).mem = some outs ∧
      .ok oc ∈ outs ∧ tr.cfg (k + 1) = (tr.cfg k).withThread H oc.thread oc.mem :=
  adv hpf hwf (henH hs h0 hpf hM hL hH hwf) j hj ht

/-- `H` never gets through its critical section: its release `incl (owner)`
reads `m` (its coherence view of `owner` is at the last write, `CInv`) and
would raise `m`. -/
theorem cs_false : ∀ d p j, p + d = 10 → 7 ≤ p → n ≤ j → ∀ t, (tr.cfg j).threads[H]? = some t →
    t.st.st.2 = pcA p → False := by
  intro d
  induction d with
  | zero =>
    intro p j hp _ hj t ht hpc
    obtain rfl : p = 10 := by omega
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := advH hs h0 hpf hM hL hH hwf _ hj ht
    obtain ⟨hT, -, -, -⟩ := hold hs h0 hpf hM hL hH hwf _ (Nat.le_trans hj hk) htk
    obtain ⟨-, -, -, v, -, hv, hm, -⟩ := s10 hT.st hT.prom hso ho hpc
    have hvm := hv (hT.inv (by decide) hpc).2
    obtain ⟨xc, hI⟩ := inv_at hs h0 hpf k
    have hmk : ((tr.cfg k).mem.finalVal OL).toNat = m := hM k (by omega)
    have := hI.N32; have := hI.xcN; have hmx : ((tr.cfg k).mem.finalVal OL).toNat ≤ xc := hI.mxc
    have := hM (k + 1) (by omega)
    simp only [Mo, he, Config.withThread, hm, finalVal_append, ite_true] at this
    rw [hvm, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth, hmk] at this
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [h1, Nat.mod_eq_of_lt (by omega : m < 2 ^ 32), Nat.mod_eq_of_lt (by omega : m + 1 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  | succ d ih =>
    intro p j hp h7 hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := advH hs h0 hpf hM hL hH hwf _ hj ht
    obtain ⟨hT, -, -, -⟩ := hold hs h0 hpf hM hL hH hwf _ (Nat.le_trans hj hk) htk
    refine ih (p + 1) (k + 1) (by omega) (by omega) (by omega) _ (wt_self htk he) ?_
    have : p = 7 ∨ p = 8 ∨ p = 9 := by omega
    rcases this with rfl | rfl | rfl
    · obtain ⟨_, -, -, hst, -⟩ := s7 hT.st hso ho hpc; rw [hst]
    · obtain ⟨_, -, -, hst, -⟩ := s8 hT.st hso ho hpc; rw [hst]
    · obtain ⟨_, -, -, hst, -⟩ := s9 hT.st hT.prom hso ho hpc; rw [hst]

theorem cs_false' (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t) {p : Nat}
    (hp : p ∈ [7, 8, 9, 10]) (hpc : t.st.st.2 = pcA p) : False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  exact cs_false hs h0 hpf hM hL hH hwf (10 - p) p j (by omega) (by omega) hj t ht hpc

/-- `H`'s spin cells (`movl (owner),%ecx`, `cmpl`, `jne`, critical section
from 7) as `TkHolderP.SpinCells`. -/
private theorem cells : TkHolderP.SpinCells Arch.tso tr.cfg OL H n m (fun s => s.st.2 = pcA 4)
    (fun s => s.st.2 = pcA 5) (fun s => s.st.2 = pcA 6) (fun s => s.st.2 = pcA 7)
    (fun s => (eax s.st.1).toNat) (fun s => (ecx s.st.1).toNat) (fun s => s.st.1.status.zf) where
  adv j hj u hu := let ⟨k, hk, h1, h2⟩ := advH hs h0 hpf hM hL hH hwf j hj hu; ⟨k, hk, u, h1, rfl, rfl, h2⟩
  tk j hj u hu _ := (hold hs h0 hpf hM hL hH hwf j hj hu).2.1
  lw := hL
  fval := hM
  cs j hj u hu hpc := cs_false' hs h0 hpf hM hL hH hwf j hj hu (p := 7) (by decide) hpc
  ld k hk u outs oc hu hso ho hpc := by
    obtain ⟨hT, -, -, -⟩ := hold hs h0 hpf hM hL hH hwf k hk hu
    obtain ⟨md, -, -, ts, v, hcx, hst, -, hv, -, -, -, -, ν, hlog⟩ := s4 hT.st hso ho hpc
    refine ⟨by rw [hst], fun hc => ?_, ts, v, ν, hlog⟩
    obtain ⟨xc, hI⟩ := inv_at hs h0 hpf k
    have := hI.N32; have := hI.xcN; have hmx : ((tr.cfg k).mem.finalVal OL).toNat ≤ xc := hI.mxc
    rw [hst]; show (ecx md).toNat = _
    rw [hcx, hv hc, BitVec.toNat_setWidth]; omega
  cmp k hk u outs oc hu hso ho hpc := by
    obtain ⟨hT, -⟩ := hold hs h0 hpf hM hL hH hwf k hk hu
    obtain ⟨md, -, -, -, hz, hst, -, -, hcoh, -⟩ := s5 hT.st hso ho hpc
    exact ⟨by rw [hst], by rw [hst]; exact hz.trans BitVec.toNat_inj.symm, hcoh⟩
  bne k hk u outs oc hu hso ho hpc := by
    obtain ⟨hT, -⟩ := hold hs h0 hpf hM hL hH hwf k hk hu
    obtain ⟨-, hst, -, hcoh, -⟩ := s6 hT.st hso ho hpc
    refine ⟨?_, hcoh⟩
    rw [hst]; by_cases hz : u.st.st.1.status.zf = true <;> simp [hz]

/-- `H` spins: positions 4–6 (7–10: `cs_false'`). -/
private theorem spinPos (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t) :
    t.st.st.2 = pcA 4 ∨ t.st.st.2 = pcA 5 ∨ t.st.st.2 = pcA 6 := by
  obtain ⟨-, -, -, p, hp, hpc, -⟩ := hold hs h0 hpf hM hL hH hwf _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | hp
  · exact .inl hpc
  · exact .inr (.inl hpc)
  · exact .inr (.inr hpc)
  · exact (cs_false' hs h0 hpf hM hL hH hwf _ hj ht (by simp only [List.mem_cons]; omega) hpc).elim

/-- In the spin loop with an up-to-date view of `owner`, `H` enters the
critical section: contradiction (`TkHolderP.SpinCells.spin_false`). -/
theorem at_false {j : Nat} (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hc : (tr.cfg j).mem.lastWrite OL ≤ t.views.getCoh OL) : False :=
  (cells hs h0 hpf hM hL hH hwf).spin_false hj ht (spinPos hs h0 hpf hM hL hH hwf j hj ht)
    (by rw [← hL j hj]; exact hc)

/-- `H` reads `owner` infinitely often (`TkHolderP.SpinCells.reads_inf`). -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.tso tr.cfg H OL ts i) :=
  (cells hs h0 hpf hM hL hH hwf).reads_inf (fun j hj _ ht => spinPos hs h0 hpf hM hL hH hwf j hj ht)
    fun j hj => let ⟨t, ht, _⟩ := hH j hj; ⟨t, ht⟩

/-- **The holder of a constant `owner` cannot exist** (memory fairness). -/
theorem holder_false (hmf : MemFair Arch.tso tr.cfg) : False := by
  obtain ⟨t, ht, -⟩ := hH n (Nat.le_refl _)
  exact memFair_lastWrite_false hmf (reads_inf hs h0 hpf hM hL hH hwf) ht fun j hj _ ht' hc =>
    at_false hs h0 hpf hM hL hH hwf hj ht' (by rw [hL j hj]; exact hc)

end Holder

end Trace

/-! ## The theorem -/

/-- **Promise-free liveness of the x64 ticket lock with an unlocked release**
(Stage 3, promise-free fragment; `ticketlock2.kl` verbatim): on a valid layout
of the image `tk2ImageV`, on every promise-free stuttering `Arch.tso` trace
from a start configuration (`Tk2StartX`: `N` workers at `StartStateTk2 {}`)
under weak
fairness and memory fairness, every waiting thread eventually leaves its spin
loop. The `ValidLayout` hypothesis is the safety theorem's; see the module
docstring. -/
theorem ticket2_x64_live_pf (fuel : Nat) : Ticket2X64.Ticket2X64LivePF fuel := by
  intro N states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i ⟨t, ht, hsp⟩
  apply Classical.byContradiction
  intro hnd
  have hwfi := weakFairInstr_of_promiseFree hpf hwf
  -- `T` holds a ticket `K`, and keeps it
  have hkT : Ticketed t := by
    simp only [Ticket2X64.tk2SpinPcsX, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hsp
    rcases hsp with h | h | h <;> exact ticketed_at h (by decide) (by decide) (by decide)
  have hper := tk_persist hs h0 hpf ht hkT
  -- `T` stays in the spin loop, so `owner ≤ K`
  have hb : ∀ j, i ≤ j → Mo tr j ≤ tk t := by
    intro j hj
    obtain ⟨t', ht', hk', htk'⟩ := hper j hj
    have hpre : t'.st.st.2 ∈ Ticket2X64.tk2PrePcsX := Classical.byContradiction fun h => hnd ⟨j, hj, t', ht', h⟩
    obtain ⟨xc, hI⟩ := inv_at hs h0 hpf j
    obtain ⟨q, hq, hpc, hinv, -⟩ := (hI.thr tid t' ht').pc
    simp only [Ticket2X64.tk2PrePcsX, List.mem_map, List.mem_range] at hpre
    obtain ⟨r, hr, e⟩ := hpre
    rw [← htk']; unfold tk
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (e.symm.trans addrOf_0) hk'.1
    · exact absurd e.symm hk'.1
    · exact absurd e.symm hk'.2
    all_goals
      (try rw [addrOf_3] at e)
      obtain rfl := addrOf_inj (by decide) hq (e.trans hpc)
      simp only [PcInv] at hinv
      first | exact hinv | exact hinv.1
  obtain ⟨n, hin, hc⟩ := evconst (Mo tr) (M_mono hs h0 hpf) (tk t) i hb
  -- `owner` is constant from `n` on, and so is its last write
  have hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite OL = (tr.cfg n).mem.lastWrite OL := by
    intro j hj
    induction hj with
    | refl => rfl
    | @step k hle ih =>
      rcases M_step hs h0 hpf k with ⟨-, e⟩ | e
      · exact e.trans ih
      · have h1 : Mo tr (k + 1) = Mo tr n := hc (k + 1) (Nat.le_succ_of_le hle)
        have h2 := hc k hle; omega
  -- the holder of `owner`
  obtain ⟨xc, hI⟩ := inv_at hs h0 hpf n
  obtain ⟨tn, htn, hkn, hktn⟩ := hper n hin
  have := hb n hin; have := hI.tkLt tid tn htn hkn
  obtain ⟨H, u, hu, hku, hkm⟩ := hI.tkSurj (Mo tr n) (by omega)
  exact holder_false hs h0 hpf (fun j hj => hc j hj) hL
    (fun j hj => let ⟨u', h1, h2, h3⟩ := tk_persist hs h0 hpf hu hku j hj; ⟨u', h1, h2, h3.trans hkm⟩) hwfi hmf

/-! ## A concrete instance: the `.kl` runner's layout -/

open Kraken.Promising.X64.EnvG.TicketX2.Concrete in
/-- `ticket2_x64_live_pf` at the `.kl` runner's layout `tk2LayoutV` (text at
`0x100000`, `next`/`owner`/`counter` at `0x1000000`/`0x1000100`/`0x1000200`):
no hypothesis left. -/
theorem ticket2_x64_live_pf_concrete (fuel : Nat) : @Ticket2X64.Ticket2X64LivePF tk2LayoutV fuel :=
  @ticket2_x64_live_pf tk2LayoutV tk2ValidV fuel

end Kraken.Promising.Live.Ticket2X64PF
