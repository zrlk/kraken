/-
The bridge spike, spinning-reader variant: the components of the relation,
progress, and `Correct`.

* `componentsL`: the components of `RelL` hold with the straight-line
  program's `witness` (`components_of`): the spinning reader's frame is the
  straight-line reader's (`f` bound; at the test and at the exit also `r`),
  given where the registers hold the source words (`RegsL`);
* `rspecL`: the spinning reader meets `RSpec` (`Spike/Bridge/Progress.lean`):
  its solo steps keep its memory, promises and phase (`loop_step_prom`); it
  certifies only with no promise (`loop_cert`); its trees (a load, `.done`
  trees, nothing) have no fault; at a loop head it can read the latest
  write, at the test it can take its register-only step;
* `progressOfL`, `correctL`: progress, and `Correct` for the existing machine
  as a target against the spinning source program `progL` from `srcInitL`,
  any knobs and memory model on the source side, any budget.
-/
import Spike.Bridge.Loop
import Spike.Bridge.Progress

namespace Spike.Bridge

open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep
open Scc.Sem (SrcSem ExtMachine Target obs Sim Correct Budget Components)

/-! ## The components -/

section Components

variable {I : ISA} {A : Arch} {F : BitVec 64} {v1 : Val} {st0 sW : I.State} {Head : I.State → Prop}
  {Mid Exit : Val → I.State → Prop} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {rF rR : I.RegId}

/-- **Where the source words live in the variant**: register `rF` holds the
flag's address in every phase of both threads, and register `rR` of the
reader holds the value read (its low 64 bits) at the test and at the exit. -/
structure RegsL (rv : I.State → I.RegId → BitVec 64) (F : BitVec 64) (st0 sW : I.State)
    (Head : I.State → Prop) (Mid Exit : Val → I.State → Prop) (rF rR : I.RegId) : Prop where
  f0 : rv st0 rF = F
  fW : rv sW rF = F
  hd : ∀ s, Head s → rv s rF = F
  md : ∀ v s, Mid v s → rv s rF = F ∧ rv s rR = v.setWidth 64
  ex : ∀ v s, Exit v s → rv s rF = F ∧ rv s rR = v.setWidth 64

/-- The spinning reader's frame is a reader frame (`RFrame`). -/
theorem RPhaseL.frame (hone : v1.toNat = 1) (hRg : RegsL rv F st0 sW Head Mid Exit rF rR) {t : Thread I}
    {th : TermRun.TTh} (h : RPhaseL F v1 Head Mid Exit t th) : RFrame F rv rF rR t th := by
  have hlt : ∀ v : Val, (v = 0 ∨ v = v1) → v.toNat < 2 ^ 64 := by
    rintro v (rfl | rfl)
    · decide
    · rw [hone]; decide
  obtain ⟨-, -, -, ⟨hh, vs, u, rfl⟩ | ⟨v, w, vs, u, hm, rfl, hw, hv⟩ | ⟨v, w, vs, u, he, rfl, hw, hv⟩⟩ := h
  · exact ⟨rfl, hRg.hd _ hh, .inl rfl⟩
  · obtain ⟨hf, hr⟩ := hRg.md v _ hm
    exact ⟨rfl, hf, .inr ⟨v, w, rfl, hw, hlt v hv, hr⟩⟩
  · obtain ⟨hf, hr⟩ := hRg.ex v _ he
    exact ⟨rfl, hf, .inr ⟨v, w, rfl, hw, hlt v (.inr hv), hr⟩⟩

variable (A rv pl) in
/-- **The components of `RelL` hold** of every related pair, with the
straight-line program's `witness`. -/
theorem componentsL (hone : v1.toNat = 1) (hRg : RegsL rv F st0 sW Head Mid Exit rF rR)
    {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) {t : (ExtMachine.ofBase I A rv pl).Cfg} {s : TermRun.Cfg}
    (hR : RelL F v1 st0 sW Head Mid Exit t.1 s) :
    Components (ExtMachine.ofBase I A rv pl) Λ (witness A rv pl F rF rR) t s := by
  obtain ⟨t0, t1, th0, th1, hc, hs, hW, -, hRd, hM, -, -⟩ := hR
  exact components_of hRg.f0 hRg.fW hone hΛ hc hs hW (hRd.frame hone hRg) hM

end Components

/-! ## Progress -/

section Progress

variable {I : ISA} (A : Arch) {F : BitVec 64} {v1 : Val} {Head : I.State → Prop}
  {Mid Exit : Val → I.State → Prop} (hL : LoopShape I F Head Mid Exit)
include hL

/-- The spinning reader's solo steps keep its memory. -/
theorem loop_step_mem {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory}
    (hph : LPhase Head Mid Exit t.st) (h : ThreadStep A tid (t, mem) q) : q.2 = mem := by
  rcases hph with hh | ⟨v, hm⟩ | ⟨v, he⟩
  · exact (loop_head_out A hL hh h).1
  · exact (loop_mid_out A hL hm h).1
  · exact absurd h (no_threadStep A (hL.ex v _ he))

/-- **The spinning reader meets `RSpec`.** -/
theorem rspecL : RSpec A F v1 (LPhase Head Mid Exit) where
  step {t mem q} hP hts := by
    obtain ⟨hp, hP'⟩ := loop_step_prom A hL (q := (t, mem)) hP hts
    exact ⟨loop_step_mem A hL hP hts, hp, hP'⟩
  cert {t mem} hP hc := loop_cert A hL hP hc
  ok {t mem outs} hP hs' m := by
    rcases hP with hh | ⟨v, hm⟩ | ⟨v, he⟩
    · obtain ⟨kl, g, hex, -⟩ := hL.hd _ hh
      exact stepOne_no_error A hex (runTree_load_ok A _ _ _ _ _ _) hs' m
    · obtain ⟨s', hex, -⟩ := hL.md v _ hm
      exact stepOne_no_error A hex (runTree_done_ok A _ _ _ _) hs' m
    · have hex : I.exec t.st = none := hL.ex v _ he
      simp [stepOne, hex] at hs'
  can {c t0 t1} hc hM hp hP hh := by
    rcases hP with hh' | ⟨v, hm⟩ | ⟨v, he⟩
    · obtain ⟨kl, g, hex, -⟩ := hL.hd _ hh'
      exact load_can_step A hc hM hp hex
    · obtain ⟨s', hex, -⟩ := hL.md v _ hm
      exact done_can_step A hc hp hex
    · simp [Thread.halted, hL.ex v _ he] at hh

variable {st0 sW st1 : I.State} (hWS : WShape I F v1 st0 sW) (hh : Head st1)
include hWS hh

/-- **Progress of the variant**: every configuration reachable from the
loaded start configuration (the reader at a loop head) has progress. -/
theorem progressOfL (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64)) :
    ProgressOf A rv pl st0 st1 F := fun _ hre _ hμ =>
  progress_of_base A hμ (baseProgressG A hWS (rspecL A hL)
    (tinvG_reach A hWS (rspecL A hL) hre (tinvG_init (.inl hh))))

/-- **`Correct` for the variant**, with every clause of `Sim` discharged: the
existing machine as a target, loading the writer's and the spinning
reader's start states and the flag's initial write; the source program
`progL` from `srcInitL`, any knobs and memory model, any budget. -/
theorem correctL {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)}
    {rF rR : I.RegId} {k : Promises.Knobs} {arch : WeakMem.Arch}
    (hRg : RegsL rv F st0 sW Head Mid Exit rF rR) {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) (hwf : Λ.WF)
    (B : Budget) :
    Correct (Target.ofBase I A rv pl) (SrcSem.ofStep progL k arch (· = srcInitL)) Λ B (asmOf st0 st1 F) := by
  refine ⟨{
    R := fun t s => RelL F v1 st0 sW Head Mid Exit t.1 s
    layout := hwf
    start := ⟨_, srcInitL, rfl, rfl, rel_initL hh⟩
    progress := ?_
    sim := fun t0 tr t h0 hr => ?_
    abort := ?_
    explicit := fun t s hR => ⟨witness A rv pl F rF rR, componentsL A rv pl hWS.one hRg hΛ hR⟩ }⟩
  · intro t0 tr t h0 hr
    obtain ⟨-, s, -, hR, -⟩ := sim_clause_loop A hWS hL (k := k) (arch := arch) hh rv pl Λ _ t0 tr t h0 hr
    cases h0
    obtain ⟨-, hre⟩ := ExtMachine.ofBase_run_inv hr
    obtain ⟨-, -, -, -, -, -, -, -, -, hM, -, -⟩ := hR
    exact ⟨progressOfL A hL hWS hh rv pl t hre _ (fun _ => rfl), inLayout_of A hΛ hM⟩
  · obtain ⟨tr', s, hs, hR, he⟩ := sim_clause_loop A hWS hL (k := k) (arch := arch) hh rv pl Λ _ t0 tr t h0 hr
    exact ⟨tr', s, hs, hR, he ▸ List.prefix_refl _⟩
  · intro t0 tr t tid es t' ak _ _ hs hab
    obtain ⟨rfl, -⟩ := ExtMachine.ofBase_step_inv hs
    cases hab

end Progress

end Spike.Bridge
