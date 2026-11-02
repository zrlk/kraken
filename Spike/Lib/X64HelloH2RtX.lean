/-
**`H1GAH0W`'s runtime fields at the self words** (hello.w, x86-64): `X64HelloH2Rt`'s `h2` memory side and its
runtime fields with main's owned words `ownGHXW` (`ownGH`'s words, main's TCB word, the worker's TCB word) in
place of `ownGH`. The side differs from `H2Rt.ms2H` in its owned words only (`ms2HX_eq`), and every field reads
the owned words only through a membership the larger `ownGHXW` keeps (`ownGH` is its prefix).

- `ms2HX`: `h2`'s memory side at `ownGHXW` (`H2Rt.ms2H` with the owned words `ownGHXW … ntA`).
- `ms2HX_eq`: `ms2HX` is `ms2H` with the owned words replaced (`rfl`).
- `stOk_own`, `ldOk_own`, `resOkA_own`, `tcbOkGA_own`, `takeOkA_own`: `StOk`, `LdOk` read no owned words;
  `ResOkA`, `TcbOkGA`, `TakeOkA` hold at any larger owned words.
- `resA_HX`, `hdrA_HX`, `tid_HX`, `tcbA_HX`, `hfld_HX`, `htk_HX`: `H2Rt`'s `resA_H2`, `hdrA_H`, `tid_H`, `tcbA_H`,
  `hfld_H`, `htk_H` at `ms2HX`.

## Unlike AArch64

AArch64's third level owns `ownGH`, so `A64HelloH2Rt`'s side needs no such twin; x86-64's main also holds its own
and the worker's TCB words (`ownSH`, `ownSWH`) up to the clone, so the root's third level owns `ownGHXW`.
-/
import Spike.Lib.X64HelloH2Rt
import Spike.Lib.X64HelloOwnSX

namespace Spike.Lib.X64.HelloPh.H2RtX

open Kraken Kraken.Promising Kraken.Promising.X64
open SccCode (helloCells)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib (PlaceWX MemSide)
open Spike.Lib.X64.Rt (RuntimeLayout TcbOkGA hdrA TakeOkA)
open Spike.Lib.X64.Rt.Reserve (ntA ResOkA)
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH tH)
open Spike.Lib.X64.HelloPh.Tcb2CallW (BandSp3H)
open Spike.Lib.X64HelloGOf2H (gWH)

/-! ## The callees' memory-side facts at larger owned words -/

section Own

variable {ms : MemSide isa} {o : State → List (Loc × Val)} {F0 F : MachineData → Prop}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region}

/-- `StOk` reads no owned words. -/
theorem stOk_own {a v : BitVec 64} (h : StOk ms F0 a v) : StOk { ms with own := o } F0 a v :=
  ⟨h.rt, h.mp, h.G, h.unmapped⟩

/-- `LdOk` reads no owned words. -/
theorem ldOk_own {a : BitVec 64} (h : LdOk ms F0 a) : LdOk { ms with own := o } F0 a :=
  ⟨h.rt, h.mp, h.unmapped⟩

/-- `ResOkA` at larger owned words. -/
theorem resOkA_own {q} (ho : ∀ s x, x ∈ ms.own s → x ∈ o s)
    (h : ResOkA ms F0 exe endPc R F q) : ResOkA { ms with own := o } F0 exe endPc R F q :=
  ⟨stOk_own h.next, fun s c hA => ho _ _ (h.own s c hA)⟩

/-- `TcbOkGA` at larger owned words. -/
theorem tcbOkGA_own {q} (ho : ∀ s x, x ∈ ms.own s → x ∈ o s)
    (h : TcbOkGA ms F0 exe endPc R F q) : TcbOkGA { ms with own := o } F0 exe endPc R F q :=
  ⟨stOk_own h.next, fun s c hA => ho _ _ (h.own s c hA)⟩

/-- `TakeOkA` at larger owned words. -/
theorem takeOkA_own {q} (ho : ∀ s x, x ∈ ms.own s → x ∈ o s)
    (h : TakeOkA ms F0 exe endPc R F q) : TakeOkA { ms with own := o } F0 exe endPc R F q :=
  ⟨stOk_own h.lock1, ldOk_own h.freeN, stOk_own h.lock0, stOk_own h.next,
    fun b s c hA => ho _ _ (h.ownLock b s c hA), fun b s c hA => ho _ _ (h.ownFreeN b s c hA),
    fun b s c hA => ho _ _ (h.ownNext b s c hA)⟩

end Own

/-! ## The side at `ownGHXW` -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Scc.Sem.X64.Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`h2`'s memory side at the self words**: `H2Rt.ms2H` with main's owned words `ownGHXW … ntA`. -/
noncomputable def ms2HX (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) :
    List TermRun.Frame → MemSide isa :=
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
    (gWH hp i (Spike.Lib.X64WakeHG.cTW hp i)) (fun s _ => ownGHXW (Ly) (ntA (Ly).lab) s)
    (Spike.Lib.X64.WakeOD.arW hp i)
    (fun _ _ _ _ _ => False) (lbl2H (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b l' b')
    (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls) l n) l' n')

variable {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}

/-- `ms2HX` is `ms2H` with the owned words `ownGHXW`. -/
theorem ms2HX_eq (fs : List TermRun.Frame) :
    ms2HX asm hp i E ls l b n l' b' n' fs =
      { H2Rt.ms2H asm hp i E ls l b n l' b' n' fs with own := fun s => ownGHXW (Ly) (ntA (Ly).lab) s } :=
  rfl

/-- `ownGH`'s words are `ownGHXW`'s. -/
theorem own_sub : ∀ s x, x ∈ (H2Rt.ms2H asm hp i E ls l b n l' b' n' []).own s →
    x ∈ ownGHXW (Ly) (ntA (Ly).lab) s :=
  fun _ _ h => List.mem_append_left _ (List.mem_append_left _ h)

set_option hygiene false in
/-- `h2`'s memory side at the self words at no frames. -/
local notation "ms2" => ms2HX asm hp i E ls l b n l' b' n' []

variable {F : MachineData → Prop} {R : Spike.Lib.Region}

section Fields

variable (hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x)
  (hstat : Λ0.static = fun _ => none)
  (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
  (hf : Fresh2H (Spike.Lib.X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n')

include hlab hstat hA13 hf in
/-- `H2Rt.resA_H2` at `ms2HX`. -/
theorem resA_HX (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none) :
    ∀ g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G × Ctl, ResOkA ms2 F (Ly).exe (Ly).endPc
      (Spike.Lib.X64.Flow.HelloWc.rARH R) F ⟨g.1, 0#64, g.2⟩ :=
  fun g => resOkA_own (own_sub asm hp i E ls) (H2Rt.resA_H2 asm hp i E ls hlab hstat hA13 hf hunN g)

include hstat hA13 hf in
/-- `H2Rt.hdrA_H` at `ms2HX`. -/
theorem hdrA_HX (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 104#64) 8 = none) :
    ∀ c0 g, StOk ms2 F (hdrA (Ly).lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36) :=
  fun c0 g => stOk_own (H2Rt.hdrA_H asm hp i E ls hstat hA13 hf hunH c0 g)

include hstat hA13 hf in
/-- `H2Rt.tid_H` at `ms2HX`. -/
theorem tid_HX (hunT : ∀ m', F m' → Mem.loadInt m'.dmem (tH (Ly).lab + 56#64) 8 = none) :
    (ms2).rt (tH (Ly).lab + 56#64).toNat ∧ (ms2).mp ⟨tH (Ly).lab + 56#64, 8⟩ true ∧
      (ms2).G ⟨tH (Ly).lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (tH (Ly).lab + 56#64) 8 = none :=
  H2Rt.tid_H asm hp i E ls hstat hA13 hf hunT

include hlab hstat hA13 hf in
/-- `H2Rt.tcbA_H` at `ms2HX`. -/
theorem tcbA_HX (hb : BandSp3H (Ly) R) (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none) :
    ∀ c0 g, TcbOkGA ms2 F (Ly).exe (Ly).endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0) :=
  fun c0 g => tcbOkGA_own (own_sub asm hp i E ls) (H2Rt.tcbA_H asm hp i E ls hlab hstat hA13 hf hb hunP c0 g)

include hstat hA13 hf in
/-- `H2Rt.hfld_H` at `ms2HX`. -/
theorem hfld_HX (hunF : ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields (tH (Ly).lab)
      (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 16384#64),
      ∀ m, F m → Mem.loadInt m.dmem (tH (Ly).lab + BitVec.ofNat 64 e.1) 8 = none) :
    ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields (tH (Ly).lab)
      (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 16384#64),
      StOk ms2 F (tH (Ly).lab + BitVec.ofNat 64 e.1) e.2 :=
  fun e he => stOk_own (H2Rt.hfld_H asm hp i E ls hstat hA13 hf hunF e he)

include hlab hstat hA13 hf in
/-- `H2Rt.htk_H` at `ms2HX`. -/
theorem htk_HX (hb : R.base.toNat + 96 = (Ly).stacksA.toNat + 16384)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) :
    ∀ (c0 : Ctl) (R' : Spike.Lib.Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-136) (-248) 8 → ∀ (g g' : Spike.Lib.X64.Flow.Ret0.AllocTcb.G),
      TakeOkA ms2 F (Ly).exe (Ly).endPc (R'.callee (-48 - 0) (-200) 8) F'
        (Spike.Lib.X64.Flow.Ret0.tiTake (Spike.Lib.X64.Flow.WakeWc.tiQ (tH (Ly).lab) c0 g) g') :=
  fun c0 R' F' hF hR g g' => takeOkA_own (own_sub asm hp i E ls)
    (H2Rt.htk_H asm hp i E ls hlab hstat hA13 hf hb hFr c0 R' F' hF hR g g')

end Fields

end Spike.Lib.X64.HelloPh.H2RtX

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.H2RtX.ms2HX_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2RtX.ms2HX_eq

/-- info: 'Spike.Lib.X64.HelloPh.H2RtX.resA_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2RtX.resA_HX

/-- info: 'Spike.Lib.X64.HelloPh.H2RtX.hdrA_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2RtX.hdrA_HX

/-- info: 'Spike.Lib.X64.HelloPh.H2RtX.tid_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2RtX.tid_HX

/-- info: 'Spike.Lib.X64.HelloPh.H2RtX.tcbA_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2RtX.tcbA_HX

/-- info: 'Spike.Lib.X64.HelloPh.H2RtX.hfld_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2RtX.hfld_HX

/-- info: 'Spike.Lib.X64.HelloPh.H2RtX.htk_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2RtX.htk_HX
