/-
**`wc_waitLoop`'s `htls` at wake's listing** (AArch64, main
after the spawn): `Spike.Lib.A64.WaitLoop.seg_waitLoop`'s premise `htls`,
the limit load `ldr x10, [x10, #8]` from node `.tls` (`x10 = tp`) to node
`.n1` (`x10 ≤ x9`) as a segment inside `TlsW` with no outside moves, at
wake's prefix (`WakeLabels.pfx`), given the limit word's facts (`LimOk` at
`tp + 8` with room up to the new frame's `sp`, `x9 = R.addr (-32)`) and the
word not the flag's address. The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `htls_of`: one frame (`seg_waitTlsLim`).
- `htls_ofPlaceOK`: at the instance (`msOf` at `wakeG (GOf2 L m0) cT`,
  `tp` the first TCB), the `LimOk` from `WakeHS.limOk_ofPlaceOK`.
-/
import Spike.Lib.A64WakeAbOffL
import Spike.Lib.A64WaitLoop
import Spike.Lib.WakeHS
import Spike.Lib.PlaceWRt

namespace Spike.Lib.A64.Flow.Worker.Wake.Htls

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open CoreLang CoreTerm
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.WaitLoop (N JE)
open Spike.Lib.A64.Flow.Worker.Wake.AbOffAt (seg_waitTlsLim)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A x29 ra tp : BitVec 64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`htls` for one frame**: the limit load from `.tls` to `.n1` inside
`TlsW`, given the limit word's `LimOk` with room up to `x9`'s address and
the word off the flag's address. -/
theorem htls_of (hexe : exe.2 = Spike.Lib.A64.WakeLabels.cellsOf wakeProg ++ exe.2.drop wakeProg.length)
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) (hF : FStable R F)
    (hL : Spike.Lib.A64.Flow.Ret0.LimOk ms F exe endPc (tp + 8#64) (R.addr (-32))) (hA : tp + 8#64 ≠ A) :
    SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0) (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty Rd A x29 ra tp .tls))
      (At exe endPc R F (N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty Rd A x29 ra tp .n1)) := by
  refine seg_waitTlsLim hp hend ?_ hF (fun _ _ h => h.2) (fun _ _ h => h.1.1) hL hA rfl
    (by show SO.le Spike.Lib.A64.WaitLoop.oX (Spike.Lib.A64.WaitLoop.oX.kill .X10) = true; decide) ?_
  · show _ = _
    rw [Spike.Lib.A64.WakeLabels.hcheck hexe]
    show _ + 4 + 4 = _
    rw [Int64.add_assoc]; rfl
  · intro σ c v hso hJ hroom
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hJ
    have h9 := hso (.reg .X9) (-32) rfl
    refine ⟨⟨h1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h2
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h3
    · simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64] using h4
    · rw [show (ldStep .X10 (v.setWidth 64) σ).regs.TPIDR_EL0 = σ.regs.TPIDR_EL0 from
        Spike.Lib.A64.KeepTP.setRegOrZr_tp _ _ _]; exact h5
    · simp only [Reg64s.getRegOrSp64, Reg64s.getXReg] at h9
      simpa [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, h9] using hroom

/-- **`htls` at the instance**: `ms` the consumer's memory side at
`wakeG (GOf2 L m0) cT` of a placed output (`L := RuntimeLayout.ofPlaceW hpl i`),
`tp` the first TCB, every frame condition inside `rtF L`, every frame's
`x9` address `(Rg g).addr (-32)` at least the limit (`hZ`), the limit word
neither the flag's target `cT` (`hcT`) nor the flag's address `A` (`hA`). -/
theorem htls_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hpl : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tq0 tq sp : List Nat}
    (h : Scc.Sem.MemRelP (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpl i).Λ lbl lsize ts tm sm tq0 tq sp)
    {rd : TermRun.Word → Prop} {own : Spike.Lib.A64Consumer.Own} {cT : Loc}
    {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}
    (hexe : exe.2 = Spike.Lib.A64.WakeLabels.cellsOf wakeProg ++ exe.2.drop wakeProg.length)
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) (hF : ∀ g, FStable (Rg g) (Fg g))
    (hFrt : ∀ g m, Fg g m → Spike.Lib.A64.Rt.rtF (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpl i) m)
    (hZ : ∀ g, (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpl i).stacksA.toNat + 4096 ≤ ((Rg g).addr (-32)).toNat)
    (hcT : (⟨(Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpl i).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT)
    (hA : (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpl i).pinA + 0#64 + 8#64 + 8#64 ≠ A) :
    let L := Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpl i
    let ms := Spike.Lib.A64Consumer.msOf L.Λ (Spike.Lib.A64.PhRec.μ L) rd
      (Spike.Lib.WakeG.wakeG (Spike.Lib.WakeGOf2.GOf2 L (Spike.Lib.A64.PhRec.m0Of L.Λ o.prog o.secs)) cT) own lbl lsize
    ∀ g, SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0) (fun _ _ => False) p lbl ms
      (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ Scc.Sem.ValRep lbl w'.val 1) A (fp g) ra (L.pinA + 0#64 + 8#64) .tls))
      (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ Scc.Sem.ValRep lbl w'.val 1) A (fp g) ra (L.pinA + 0#64 + 8#64) .n1)) :=
  fun g => htls_of hexe hp hend (hF g)
    (Spike.Lib.WakeHS.limOk_ofPlaceOK hpl i h hcT (hFrt g) (hZ g)) hA

/-- info: 'Spike.Lib.A64.Flow.Worker.Wake.Htls.htls_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms htls_ofPlaceOK

end Spike.Lib.A64.Flow.Worker.Wake.Htls
