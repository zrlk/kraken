/-
**The second `scc_rt_stack_take` call's load node and take site inside
`W0`** (x86-64; twin of `Spike/Lib/A64WakeTi2L2.lean`, the `hatA` ti
discharger): the free count's load and the take site of the call from the
second `scc_rt_thread_init` (on a pool stack) inside the level
`StartWf.WS`, as `StartTi.nodeI_WSld` / `siteI_WS` with the frame on the
pool (`Ti2.BandP`) and `ownG` at `own2b` (`Ti2.node2_own`, `site2_own`).

- `node2_WSld`: the free count's load inside `WS`.
- `site2_WS`: the take site inside `WS`.

**Unlike AArch64**: AArch64's `node2_WSswp` and `node2_WSstlr` are
`StartTi.node2_WSxchg` and `node2_WSst` (`Spike/Lib/X64WakeTi2L.lean`;
x86-64's lock is `xchgq` and its release a plain `movq`); `node2_WSldr` is
`node2_WSld` (`movq i(%b), %r`, `ldDir`); the site's `nop` is
`op64 (.nop 1)` of size `z`; the rest as `X64WakeTi2L` (no `hal`, frame
high end `8`, `z`-byte successors, `Keep` on `%rsp`/`%rbp`).
-/
import Spike.Lib.X64WakeTi2L
import Spike.Lib.X64WakeStartTiL2

namespace Spike.Lib.X64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize SFacts)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND NodeW At ldDir bAddr)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh.StartWf (WS pfxM)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64.WakePh.Ti2 (BandP node2_own site2_own)
open Kraken.Promising.Lower.X64 (op64)

section Gen

variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range} {Tk : State → Prop}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop} {klo : Int}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 [])
  (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.X64.DFrame R m m' → Pl m')
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandP L R klo)

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd

/-- **The free count's load inside `WS`** (as `node2_WS`): `movq i(%b), %r`
of a word unmapped in private memory (`ha`). -/
theorem node2_WSld {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(ldDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcN n.pc ∧ PcI (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.WakeWf.nodeW_wfLd (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The take site inside `WS`**: the `nop` (`hb`), its states' `SFactsSt` at
the second instance (`hS`), off the abort sites (`habt`), its successors
keeping `%rsp` and `%rbp` `z` bytes on (`hk`), its pc and the next in the
callees (`hpc`), its static `%rsp` offset in `[klo, 8]` (`hso`), its abort
phases' check (`hph`), its controls `c0` (`hJ`); `X0` at the site's states
from their take range, frame and region cells (`hXs`), off it by `hX0`. -/
theorem site2_WS {n : ND} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(op64 (.nop 1), z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
    (habt : ∀ k x, (Spike.Lib.X64.PhRec.μ L).abortAt k = some x → n.pc.toBitVec.toNat ≠ x)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcI n.pc ∧ PcI (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 →
      (∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) → X0 s) :
    ∀ s c, At L.exe L.endPc R F n s c → WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.WakeWf.site_wf (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) (Dt := Dt) hI (hp ▸ hb) he (site2_own hlab hbd hS hk hpc hso) habt
    (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)))
  intro s c hA
  have hpc' := hA.2.2.2.1
  have hx : X0 s := by
    by_cases hs : pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
    · obtain ⟨-, -, -, -, σ, hAb, hF, -⟩ := id hA
      refine hXs s hs ((hS s c hA).site _ hsite hs).2.2.2.1 hF fun k hk => ?_
      obtain ⟨j, hj, -⟩ := hAb.slot k hk
      rw [hj]; rfl
    · exact hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1)) hs
  exact ⟨.inl rfl, hx, hw s c hA⟩

end Gen

end Spike.Lib.X64.WakePh.StartTi

/-- info: 'Spike.Lib.X64.WakePh.StartTi.node2_WSld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.node2_WSld

/-- info: 'Spike.Lib.X64.WakePh.StartTi.site2_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.site2_WS
