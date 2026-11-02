/-
**The second `scc_rt_thread_init` call writes off the arena** (x86-64): the per-state fact `HelloW2.OffW ar s` at
every node of hello's second thread-init call, conjoined to `StartTi.ti2_WSPH`'s level `WSH`, so that the level
lift at the clone (`HelloW2.w2H_of_wsh`'s `OffW` antecedent) is fed by the segment itself and no root field has to
assert it.

`WSH`'s arena conjunct (`WakeWf.Wf`'s `ArenaWr`) says every write off the counter is `ArenaW` at the level's
placement and sizes or is in the context; `ti2_WSPH` holds at any context and sizes. At the empty context and the
sizes `fun _ => 0` the context disjunct is gone, a placed label has no cells (`lrange` empty), and the allocation
disjuncts need a held counter, which the ti nodes' control `c0` (main's source at the box's fence, `QBH`) does not
hold: what is left of `ArenaW` is "off the arena"; the counter is not written because the context is empty.

- `offW_of_wsh`: `OffW` from `WSH` at the empty context and zero sizes, at a control holding nothing.
- `takeWP_c0'`, `tiWAtP_c0'`: `Ti2C0.takeW_c0` / `StartTi.tiWAt_c0` with `hW` read at the dummy control only.
- `takeWP_and`, `tiWAtP_and`: the obligations at two levels combine.
- `ti2_offW`: `ti2_WSPH` at that context and sizes, read as `TiWAtP (fun s _ => OffW ar s)`.
- `ti2_WSPH_off`: `ti2_WSPH`'s obligations inside `WSH ∧ OffW`.
- `offW_pool`: the real pool is off the real arena (non-vacuity of the conjunct's discharge at the root: the
  frames' and the TCB's words the call writes lie in the stack pool and in `pinned`, both disjoint from the heap
  and the counter's `.data` word).

**Unlike AArch64**: the obligations are `Rt.TakeWP` / `Rt.TiWAtP … x8L P` (`P` at the take site, the call
returning to `.x8`) rather than `TakeW … P` / `TiW … P`, so the control moves are stated for those
(`takeWP_c0'`, `tiWAtP_c0'`, `takeWP_and`, `tiWAtP_and`); `WSH` is `W0 … []`, its `Wf` the third conjunct; the
pool lemma reads `PlaceWX` / `RuntimeLayout.ofPlaceWX` / `X64.WakeOD.arW`; the ti nodes' control is `QBH`'s
(the box's fence; AArch64: `SpawnSrcH`'s).
-/
import Spike.Lib.X64HelloTi2P
import Spike.Lib.X64HelloW2Weak
import Spike.Lib.X64WakeTi2C0
import Spike.Lib.X64WakeWcMidW
import Spike.Lib.X64WakeOD
import Spike.Lib.X64PlaceW
import Spike.Lib.Rt.X64ArenaOfPlaceW
import Spike.Lib.X64HelloHMid

namespace Spike.Lib.X64.HelloPh.Ti2OffW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout TakeWP TiWAtP TiWAt tiNAt x8L)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.Flow.Ret0 (TK TI TakeG TiG TakeW StackM stacksA takeNG)
open Spike.Lib (Arena FragS Ctl)
open Spike.Lib.X64.WakePh.Ti2 (BandP)
open Spike.Lib.X64.WakePh (inPc WSep)
open Spike.Lib.X64.HelloW2 (OffW)
open Spike.Lib.X64.HelloPh.StartTi (ti2_WSPH tiJAt_c0)

/-- **`OffW` from `WSH` at the empty context and zero sizes** (module doc), at a control holding nothing (`hh`):
the counter is not written (`Wf`'s counter row at the empty context), and `ArenaW` at zero sizes with no held
counter is "off the arena". -/
theorem offW_of_wsh {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {lbl : Lbl}
    {frM : TermRun.Frame} {X0 : State → Prop} {s : State} {c : Ctl}
    (h : WSH L a ar p Dt Cl (fun _ _ _ => False) lbl (fun _ => 0) frM X0 s c) (hh : c.hold = none) : OffW ar s := by
  obtain ⟨-, -, -, -, -, -, hAW, hctr, -, -⟩ := h.2.2
  intro Lw hw
  have hne : Lw ≠ ar.ctrLoc := fun e => hctr (e ▸ hw)
  refine ⟨hne, ?_⟩
  rcases hAW c [] (Spike.Lib.FrameRun.refl _) Lw hw hne with h | ⟨h, -⟩
  · rcases h with h | h | ⟨l, b, -, hc⟩ | ⟨old, x, aa, τ, e, ta, ws, k, hhold, -⟩ | ⟨-, old, x, aa, e, ty, ws, hhold, -⟩
    · exact absurd h hne
    · exact h
    · simp only [Scc.Sem.lrange, Range.contains] at hc; omega
    · rw [hh] at hhold; cases hhold
    · rw [hh] at hhold; cases hhold
  · exact h.elim

/-! ## The control moves reading the dummy control only -/

section C0

open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.WakePh.Ti2C0 (blkW_mapC nodeW_mapC takeJ_c0)

variable {W W' : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F M P : MachineData → Prop}

/-- **`Ti2C0.takeW_c0` at `Rt.TakeWP`, with `hW` read at the dummy control only**: `W` at `c0'` gives `W'` at
every control. -/
theorem takeWP_c0' {q : TakeG} {c0' : Ctl} (hW : ∀ s c, W s c0' → W' s c)
    (h : ∀ i, TakeWP W K exe endPc R F M { q with c0 := c0' } P i) : ∀ i, TakeWP W' K exe endPc R F M q P i := by
  intro i
  have hi := h i
  have hB : ∀ {F' : MachineData → Prop} {n n' : ND} {blk}, BlkW W K exe endPc R F' n' blk → n'.pc = n.pc →
      n'.o = n.o → (∀ σ c, n.J σ c → n'.J σ c0') → BlkW W' K exe endPc R F' n blk :=
    fun h hp ho hJ => blkW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  have hN : ∀ {F' : MachineData → Prop} {n n' : ND}, NodeW W K exe endPc R F' n' → n'.pc = n.pc → n'.o = n.o →
      (∀ σ c, n.J σ c → n'.J σ c0') → NodeW W' K exe endPc R F' n :=
    fun h hp ho hJ => nodeW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  cases i <;> dsimp only [TakeWP, TakeW] at hi ⊢
  case site =>
    exact fun s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ => hW s c (hi s c0' ⟨he, hn, hd, hp, σ, hA, hF, takeJ_c0 hJ⟩)
  case d0 | d26 | d52 | swp | ldn | b0 | unl | b31 | nxt | ok0 => exact hN hi rfl rfl (fun _ _ => takeJ_c0)
  all_goals exact hB hi rfl rfl (fun _ _ => takeJ_c0)

/-- **`StartTi.tiWAt_c0` at `Rt.TiWAtP`, with `hW` read at the dummy control only** (its call's by
`takeWP_c0'`). -/
theorem tiWAtP_c0' {q : TiG} {x : Label} {c0' : Ctl} (hW : ∀ s c, W s c0' → W' s c)
    (h : ∀ i, TiWAtP W K exe endPc R F M { q with c0 := c0' } x P i) : ∀ i, TiWAtP W' K exe endPc R F M q x P i := by
  intro i
  have hi := h i
  have hB : ∀ {F' : MachineData → Prop} {n n' : ND} {blk}, BlkW W K exe endPc R F' n' blk → n'.pc = n.pc →
      n'.o = n.o → (∀ σ c, n.J σ c → n'.J σ c0') → BlkW W' K exe endPc R F' n blk :=
    fun h hp ho hJ => blkW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  have hN : ∀ {F' : MachineData → Prop} {n n' : ND}, NodeW W K exe endPc R F' n' → n'.pc = n.pc → n'.o = n.o →
      (∀ σ c, n.J σ c → n'.J σ c0') → NodeW W' K exe endPc R F' n :=
    fun h hp ho hJ => nodeW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  cases i <;> dsimp only [TiWAtP, TiWAt] at hi ⊢
  case call => exact fun g hg j => takeWP_c0' hW (hi g hg) j
  case x7 => exact hB hi rfl rfl (fun _ _ h => tiJAt_c0 (x := x) (i := .x7) h)
  case st0 | st1 | st2 | st3 | st4 | st5 => exact hN hi rfl rfl (fun _ _ => tiJAt_c0)
  all_goals exact hB hi rfl rfl (fun _ _ => tiJAt_c0)

/-- **`scc_rt_stack_take`'s obligations at two levels combine** (`WakeWc.blkW_and` / `nodeW_and`, the first's
outside move). -/
theorem takeWP_and {W₂ : Spike.Lib.Frag isa} {K₂ : State → State → Prop} {q : TakeG} {i : TK}
    (h₁ : TakeWP W K exe endPc R F M q P i) (h₂ : TakeWP W₂ K₂ exe endPc R F M q P i) :
    TakeWP (fun s c => W s c ∧ W₂ s c) K exe endPc R F M q P i := by
  cases i <;> dsimp only [TakeWP, TakeW] at h₁ h₂ ⊢ <;>
    first
    | exact Spike.Lib.X64.Flow.WakeWc.blkW_and h₁ h₂
    | exact Spike.Lib.X64.Flow.WakeWc.nodeW_and h₁ h₂
    | exact fun s c hA => ⟨h₁ s c hA, h₂ s c hA⟩

/-- **`scc_rt_thread_init`'s obligations at two levels combine.** -/
theorem tiWAtP_and {W₂ : Spike.Lib.Frag isa} {K₂ : State → State → Prop} {q : TiG} {x : Label} {i : TI}
    (h₁ : TiWAtP W K exe endPc R F M q x P i) (h₂ : TiWAtP W₂ K₂ exe endPc R F M q x P i) :
    TiWAtP (fun s c => W s c ∧ W₂ s c) K exe endPc R F M q x P i := by
  cases i <;> dsimp only [TiWAtP, TiWAt] at h₁ h₂ ⊢ <;>
    first
    | exact Spike.Lib.X64.Flow.WakeWc.blkW_and h₁ h₂
    | exact Spike.Lib.X64.Flow.WakeWc.nodeW_and h₁ h₂
    | exact fun g hg j => takeWP_and (h₁ g hg j) (h₂ g hg j)

end C0

section Gen

variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 [])
  (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.X64.DFrame R m m' → Pl m')
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbdI : BandP L R (-248))

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbdI

/-- **The second thread init's node obligations inside `OffW`** (`ti2_WSPH` at the empty context and zero
sizes, `offW_of_wsh`; its premises `ti2_WSPH`'s but the control's hold, `hh`). -/
theorem ti2_offW (Dt : State → Prop) (frM : TermRun.Frame) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TiG) (hh : c0.hold = none)
    (hmF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb,
      Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨b, 8⟩ = true)
    (hunF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hnoF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ j w, (⟨b, 8⟩, w) ∉ Spike.Lib.X64.HelloPh.own2bH L a j)
    (hra : q.g.ra = (L.lab ".Lwc_main.x25").toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hSMt : Spike.Lib.X64.FStable (R.callee (-48 - 0) (-200) 8) (StackM rS))
    (hoffT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb,
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    {P : MachineData → Prop}
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 →
      (∀ k, (R.callee (-48 - 0) (-200) 8).Off k →
        (Mem.loadInt s.st.1.dmem ((R.callee (-48 - 0) (-200) 8).addr k) 8).isSome) → X0 s) :
    ∀ i, TiWAtP (fun s _ => OffW ar s) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q x8L P i := by
  exact tiWAtP_c0' (c0' := c0) (fun _ _ hw => offW_of_wsh hw hh)
    (ti2_WSPH (Ctx := fun _ _ _ => False) (lsize := fun _ => 0) (Dt := Dt) (frM := frM) hp hlo hlab hsite hcl hc0
      hpl0 hPl hX0 hbdI hΛ hs hro hR hRlo hhi hFr { q with c0 := c0 } rfl hmF hunF hnoF hra hrS hsub hSM hSMt
      hoffT hoffL hoffX hXs)

/-- **`ti2_WSPH`'s obligations inside `WSH ∧ OffW`** (`tiWAtP_and` of `ti2_WSPH` and `ti2_offW`). -/
theorem ti2_WSPH_off (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (q : TiG) (hq : q.c0 = c0) (hh : c0.hold = none)
    (hmF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb,
      Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨b, 8⟩ = true)
    (hunF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hnoF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ j w, (⟨b, 8⟩, w) ∉ Spike.Lib.X64.HelloPh.own2bH L a j)
    (hra : q.g.ra = (L.lab ".Lwc_main.x25").toBitVec)
    (hrS : rS = ⟨(stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hSMt : Spike.Lib.X64.FStable (R.callee (-48 - 0) (-200) 8) (StackM rS))
    (hoffT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb,
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    {P : MachineData → Prop}
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 →
      (∀ k, (R.callee (-48 - 0) (-200) 8).Off k →
        (Mem.loadInt s.st.1.dmem ((R.callee (-48 - 0) (-200) 8).addr k) 8).isSome) → X0 s) :
    ∀ i, TiWAtP (fun s c => WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c ∧ OffW ar s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (StackM rS) q x8L P i := by
  intro i
  have hO := ti2_offW hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbdI Dt frM hΛ hs hro hR hRlo hhi hFr q hh hmF hunF
    hnoF hra hrS hsub hSM hSMt hoffT hoffL hoffX hXs i
  have hW := ti2_WSPH (Ctx := Ctx) (lsize := lsize) (Dt := Dt) (frM := frM) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0
    hbdI hΛ hs hro hR hRlo hhi hFr q hq hmF hunF hnoF hra hrS hsub hSM hSMt hoffT hoffL hoffX hXs i
  exact tiWAtP_and hW hO

end Gen

/-! ## The real pool is off the real arena (non-vacuity) -/

section Pool

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

/-- **A word in the stack pool is off `arW`'s cells and its counter** at the root's layout: the arena is inside
`.heap` (`arOf_sub`), the counter in `.data` (`ctr_item_of_placeW`), both disjoint from the pool (`WF.disjoint`).
The frames the thread init and the take write lie in the pool (`Ti2Hat.hti_H`'s `hsub`), the TCB's words, the
lock and the next cursor are `hoffT`/`hoffL`/`hoffX` (`HrdArena.offH_own`): this is the discharge `OffW`
abstracts at every write of the call. -/
theorem offW_pool (hc : Spike.Lib.X64.Rt.CtrZ o) :
    ∀ a : BitVec 64, (Ly).Λ.stackPool.contains a.toNat →
      ¬ ((AR).heap ≤ a.toNat ∧ a.toNat < (AR).heap + 16 * (AR).cells) ∧ (⟨a, 8⟩ : Loc) ≠ (AR).ctrLoc := by
  intro a ha
  have hs : (Scc.Sem.Range.mk (Spike.Lib.X64.Rt.arOf (Ly).Λ).heap (16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).cells)).Sub
      (Ly).Λ.heap := Spike.Lib.X64.Rt.ArenaW.arOf_sub (Spike.Lib.PlaceWX.link i hpw)
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  have hH := hwf.disjoint.2.2.2.2.2.1
  have hD := hwf.disjoint.2.2.2.2.1
  obtain ⟨hc1, hc2, -⟩ := Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceWX.link i hpw) hc
  have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
  have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceWX.link i hpw)
  have hct : (AR).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  change (Ly).Λ.stackPool.contains a.toNat at ha
  refine ⟨?_, fun h => ?_⟩
  · change ¬ ((Spike.Lib.X64.Rt.arOf (Ly).Λ).heap ≤ a.toNat ∧
      a.toNat < (Spike.Lib.X64.Rt.arOf (Ly).Λ).heap + 16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).cells)
    simp only [Scc.Sem.Range.Sub, Scc.Sem.Range.Disjoint, Scc.Sem.Range.contains] at hs hH ha
    omega
  · have ha' : a = BitVec.ofNat 64 (AR).ctr := congrArg Loc.addr h
    have := congrArg BitVec.toNat ha'
    rw [BitVec.toNat_ofNat, hct, Nat.mod_eq_of_lt (by omega)] at this
    simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.contains] at hD ha
    omega

end Pool

/-- **`offW_of_wsh`'s hold premise at the ti nodes' control**: main's source at the box's fence (`QBH`, the
control `MidG (QBH …)` pins) holds nothing. -/
example {l l' : WeakMem.AllocLabel} {b A : Nat} {ws : List TermRun.Word} {c : Ctl}
    (h : Spike.Lib.X64HelloHMid.QBH l b ws l' A c) : c.hold = none := h.2.2.2.1

end Spike.Lib.X64.HelloPh.Ti2OffW

/-- info: 'Spike.Lib.X64.HelloPh.Ti2OffW.offW_of_wsh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2OffW.offW_of_wsh

/-- info: 'Spike.Lib.X64.HelloPh.Ti2OffW.tiWAtP_c0'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2OffW.tiWAtP_c0'

/-- info: 'Spike.Lib.X64.HelloPh.Ti2OffW.tiWAtP_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2OffW.tiWAtP_and

/-- info: 'Spike.Lib.X64.HelloPh.Ti2OffW.ti2_offW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2OffW.ti2_offW

/-- info: 'Spike.Lib.X64.HelloPh.Ti2OffW.ti2_WSPH_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2OffW.ti2_WSPH_off

/-- info: 'Spike.Lib.X64.HelloPh.Ti2OffW.offW_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2OffW.offW_pool
