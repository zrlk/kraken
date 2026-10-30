/-
**wake.w on AArch64: the concrete instance data after the spawn** (hello
plan 1.6). The ghost record, both threads' memory side, the
location data, main's side `MSide`, and `wakeQ` at them, for a placed
output (`L := RuntimeLayout.ofPlaceW hp i`, its canonical memory `m0`).

- `Gh`: the ghost record `ι`: the spawn's message bound `T`, source size `S`
  and placement `lbl`/`lsize`; the flag's source address `cS` and target
  word `cT`; main's and the worker's pointer words for `c` (`cwM`, `cwW`);
  main's permit word `pT`.
- `wakeSR g`: the spawn record `⟨T, S, lbl, lsize⟩`.
- `wakeMs g`: **both threads' memory side**: the consumer's `msOf` at
  read side the numbers (`∃ n, w.val = .num n`: the source's flag load
  reads a number, `WCompat0.rd1`; so the wait loop's `Past` word is one,
  `rd_num`), value invariant `wakeG (GOf2 L m0) cT`, no
  owned word, the spawn's placement, with its runtime writes narrowed to
  words outside every placed label (`mpW0`, `mpW`).
- `wakeLocs g`, `wakeLocs_ok`: no owned word, each thread's other
  footprint the words `wakeMs` lets it write; `wakeG' g`.
- `hrt8_of_limOk`: `LimOk`'s runtime fact under `wakeMs` is
  `A64WakeMainS.tlsW_mainR`'s `hrt8`.
- `mainW lab g`: main's state predicate after the spawn (`AbOffA lab`, the
  source off its return); `mainInv`: the union of the invariants closed under
  main's rows inside it (closed: `mainInv_closed`; holds at any state of a
  closed invariant inside `mainW`: `mainInv_of`).
- `mainWR`: `mainW` with the state's writes released (`A64.Flow.RelWS`),
  the source's label words mapped in `K0` (`LabMapped`), its system calls
  `futex`/`exit_group` (`MainSys`) and the flag load's facts (`FlagW`).
- `wakeM lab μT hoff`: **main's `MSide`** (`Mi := mainInv … (mainWR …)`, `off` from
  `hoff`; at `L`, `hoff` is `A64AbOffL.off_of_A_ofPlaceOK`).
- `wakeQI`: `WakeQ.wakeQ` at these.
- Fields: `lbl0_I`, `K0_I`, `G0_I`, `own0_I`, `hMμ_I`, `live0_I`, `relW0_I`, `hhalt0_I`,
  `labMapped_I`, `hmapM_I`, `noSite0_I`, `noWrite0_I`, `flagLd_I`, `mpW0_I`, `mpW_I`, `cTfoot_I`, `cSfrz_I`,
  `footLab_I` (`rd1`/`noProm0`/`abortAt0`/`cw0`: `WakeInstFields`).
-/
import Spike.Lib.WakeQ
import Spike.Lib.A64StartOfPlaceOK
import Spike.Lib.A64AbOffL
import Spike.Lib.WakeG
import Spike.Lib.WakeGOf2
import Spike.Lib.WakeP
import Spike.Lib.A64WideKeep
import Spike.Lib.A64RelWS
import Spike.Lib.WakeMappedRow
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeInst

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeP Spike.Lib.WakeT1
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (GOf m0Of)
open Spike.Lib.A64Consumer (msOf K0)
open Spike.Lib.WakeMLive (wlRet)

/-- **The ghost record** of the two-thread phase. -/
structure Gh where
  /-- The target memory's last message at the spawn. -/
  T : Nat
  /-- The source memory's size at the spawn. -/
  S : Nat
  /-- The placement at the spawn. -/
  lbl : WeakMem.AllocLabel → Option Nat
  lsize : WeakMem.AllocLabel → Nat
  /-- The flag's source address and target word. -/
  cS : WeakMem.Address
  cT : Loc
  /-- main's and the worker's pointer words for `c`. -/
  cwM : TermRun.Word
  cwW : TermRun.Word
  /-- main's park permit word. -/
  pT : Loc

/-- **The spawn record.** -/
def wakeSR (g : Gh) : SpawnRec := ⟨g.T, g.S, g.lbl, g.lsize⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The value invariant**: the consumer's with the second TCB's limit word
also pinned (`WakeGOf2.GOf2`, the child's prologue bound), with any value at
the flag's word. -/
def wakeG' (g : Gh) : Loc → Val → Prop :=
  WakeG.wakeG (WakeGOf2.GOf2 (RuntimeLayout.ofPlaceW hp i)
    (m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs)) g.cT

/-- **Both threads' memory side**: `msOf` (read side the numbers, value
invariant `wakeG'`, no owned word, the spawn's placement) with its runtime
writes narrowed to words outside every placed label. -/
def wakeMs (g : Gh) : MemSide isaLSE2 :=
  { msOf (RuntimeLayout.ofPlaceW hp i).Λ (Spike.Lib.A64.PhRec.μ (RuntimeLayout.ofPlaceW hp i))
      (fun w => ∃ n, w.val = .num n)
      (wakeG' hp i g) (fun _ => []) g.lbl g.lsize with
    mp := fun L w => Scc.Sem.Kernel.mapped (K0 (RuntimeLayout.ofPlaceW hp i).Λ) w L = true ∧
      (w = true → Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared L ∧ ¬ InLabel g.lbl g.lsize L) }

/-- **A word `wakeMs` reads representing `1` is the number `1`** (`hd1` at `MainPieces.hexit`). -/
theorem rd_num (g : Gh) (w' : TermRun.Word) (hr : (wakeMs hp i g).rd w') (hv : ValRep g.lbl w'.val 1) :
    w'.val = .num 1 := by
  obtain ⟨n, hn⟩ := hr
  rw [hn] at hv ⊢
  rw [hv.2]

/-- **The location data**: no owned word; each thread's other footprint
words the runtime words `wakeMs` lets it write. -/
def wakeLocs (g : Gh) : WakeLocs where
  lbl := g.lbl
  lsize := g.lsize
  cT := g.cT
  cS := g.cS
  own _ _ := False
  priv _ L := (wakeMs hp i g).mp L true

/-- `wakeLocs`' separation facts. -/
theorem wakeLocs_ok (g : Gh) : (wakeLocs hp i g).OK where
  disj _ _ _ _ _ _ _ h := h
  own_nlab _ _ _ h := h.elim
  priv_nlab _ _ _ h := (h.2 rfl).2
  c_own h := h

/-- **The limit word outside every placed label** (`A64WakeMainS.tlsW_mainR`'s
`hrt8`): `LimOk`'s runtime fact under `wakeMs`, `MemSide.ofLabels`'s `rt`. -/
theorem hrt8_of_limOk (g : Gh) {F : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {a Z : BitVec 64} (h : Spike.Lib.A64.Flow.Ret0.LimOk (wakeMs hp i g) F exe endPc a Z) :
    ¬ ∃ l b, g.lbl l = some b ∧ (Scc.Sem.lrange g.lsize l b).contains a.toNat :=
  h.rt

end Inst

/-! ## main's side -/

/-- **main's state predicate after the spawn**: off every abort exit and the
transfer sites, the source off its return, the state wide on the loaded
executable `exe` (`WideX`), and the source's environment placed at the
spawn's placement `lbl` (`Placed`). Later conjuncts are appended at the end so
the projections stay stable. -/
def mainW (lab : String → Int64) (exe : _root_.Executable) (Λ : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) : Frag isaLSE2 :=
  fun s c => Spike.Lib.A64WakeOff.AbOffA lab s c ∧ c.term ≠ wlRet ∧
    Spike.Lib.A64.WideKeep.WideX exe s ∧ Spike.Lib.A64Consumer.Placed Λ lbl s c

/-- **main's system calls**: at a system call the number in `x8` is
`futex` (`98`, the park) or `exit_group` (`94`). -/
def MainSys (s : State) : Prop :=
  abi.atSys s = true → s.st.1.regs.X8.toNat = 98 ∨ s.st.1.regs.X8.toNat = 94

/-- **main's flag load** (`WCompat0.flagLd`'s facts) at placement
`lbl`/`lsize`, `q` the pc after the flag's `ldar` (`waitLoop`'s check):
- at `wlIf`, `d` is bound to a word representing `1` (`FE`);
- at `wlBody`, `c` is bound to one untagged locative inside its placed
  label (`FA`);
- at `wlBody`, a load of the word `c` represents continues, on every value,
  at `q` with the value's low 64 bits in `x9` (`FG`);
- at `wlBody` and `q`, `x9` is not `1` (`FX`). -/
def FlagW (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (q : Int64)
    (s : State) (c : Ctl) : Prop :=
  (c.term = WakeM0.wlIf → ∀ t w', TermRun.lookupE c.env "d" = some (t, [w']) → ValRep lbl w'.val 1) ∧
  (c.term = WakeM0.wlBody → ∃ t w sa, TermRun.lookupE c.env "c" = some (t, [w]) ∧ w.val = .loc sa 0 ∧
    (lbl sa.label).isSome ∧ sa.offset < lsize sa.label) ∧
  (c.term = WakeM0.wlBody → ∀ t w (A' : BitVec 64) kl (k' : Val → EvTree State),
    TermRun.lookupE c.env "c" = some (t, [w]) → ValRep lbl w.val A'.toNat →
    isaLSE2.exec s = some (.load kl false ⟨A', 8⟩ k') →
    ∀ v, ∃ s', k' v = .done s' ∧ s'.st.2 = q ∧ (s'.st.1.regs.getXReg .X9).toBitVec = v.setWidth 64) ∧
  (c.term = WakeM0.wlBody → s.st.2 = q → (s.st.1.regs.getXReg .X9).toBitVec ≠ 1#64)

/-- **main's state predicate after the spawn, with its writes released and
its label words mapped**: `mainW`, every event tree of the state's
instruction `RelW1 armv8` (`A64.Flow.RelWS`: at most one write, a release
write), the source's label words mapped in `K0 Λ`
(`WakeMappedRow.LabMapped`), its system calls `futex` or `exit_group`
(`MainSys`), and the flag load's facts at `q` the pc after `waitLoop`'s
`ldar` (`FlagW`; the label `pfx ++ ".0_entry"` is spelled out, as
`A64.WakeLabels.pfx` is not imported here). -/
def mainWR (lab : String → Int64) (exe : _root_.Executable) (Λ : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Frag isaLSE2 :=
  fun s c => mainW lab exe Λ lbl s c ∧ Spike.Lib.A64.Flow.RelWS s ∧
    Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) c ∧ MainSys s ∧
    -- `A64.WakeLabels.pfx ++ ".0_entry"`, plus the `ldar`'s 2 cells
    FlagW lbl lsize (lab (".L20_wc_waitLoop" ++ ".0_entry") + 4 + 4) s c

/-- **The union of the invariants closed under main's rows inside `W`.** -/
def mainInv (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isaLSE2) (W : Frag isaLSE2) : Frag isaLSE2 :=
  fun s c => ∃ inv : Frag isaLSE2, (∀ s c, inv s c → OutL wakeSrc lbl ms inv s c) ∧
    (∀ s c, inv s c → W s c) ∧ inv s c

theorem mainInv_closed {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {W : Frag isaLSE2} :
    ∀ s c, mainInv lbl ms W s c → OutL wakeSrc lbl ms (mainInv lbl ms W) s c := by
  rintro s c ⟨inv, hcl, hW, hi⟩
  exact (hcl s c hi).mono fun s c h => ⟨inv, hcl, hW, h⟩

theorem mainInv_W {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {W : Frag isaLSE2} :
    ∀ s c, mainInv lbl ms W s c → W s c :=
  fun s c ⟨_, _, hW, hi⟩ => hW s c hi

/-- A state of an invariant closed under the rows inside `W` is in
`mainInv` (`SegLW.closed`'s output). -/
theorem mainInv_of {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {W : Frag isaLSE2}
    {inv : Frag isaLSE2} (hW : ∀ s c, inv s c → W s c) (hcl : ∀ s c, inv s c → OutL wakeSrc lbl ms inv s c)
    {s : isaLSE2.State} {c : Ctl} (h : inv s c) : mainInv lbl ms W s c :=
  ⟨inv, hcl, hW, h⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **main's side** at labels `lab` and marks `μT`, given that `AbOffA lab`
is off every abort site of `μT` (`hoff`), over the ghost records satisfying
`ok` (the consumer's well-formedness predicate on `Gh`). -/
def wakeM (ok : Gh → Prop) (lab : String → Int64) (μT : Marks)
    (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a) :
    WakeM0.MSide {g : Gh // ok g} where
  lbl g := g.1.lbl
  ms g := wakeMs hp i g.1
  Mi g := mainInv g.1.lbl (wakeMs hp i g.1)
    (mainWR lab (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ g.1.lbl g.1.lsize)
  closed _ := mainInv_closed
  cw g := g.1.cwM
  μ := μT
  off _ s c h := hoff s c (mainInv_W s c h).1.1

/-- **wake's relation** at the instance (`R1`, the worker's side `D`, the
marks `μT` of `P`'s no-promise test and `KR`'s ranges given), over the ghost
records satisfying `ok`. -/
def wakeQI (ok : Gh → Prop) (arch : WeakMem.Arch) (R1 : WakeA64.Cfg → TermRun.Cfg → Prop) (μT : Marks)
    (M : WakeM0.MSide {g : Gh // ok g}) (D : WakeW1.WSide {g : Gh // ok g}) (r0 r1 : {g : Gh // ok g} → Range) :
    WakeRel :=
  WakeQ.wakeQ arch R1 {g : Gh // ok g} (wakeSR ·.1) (·.1.cT) (·.1.cS) (·.1.pT)
    (fun g => wakeP abi μT (wakeLocs hp i g.1)) (fun g => wakeG' hp i g.1) M D r0 r1

/-! ## The definitional fields -/

variable {ok : Gh → Prop} {lab : String → Int64} {μT : Marks}
  {hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a}
  {arch : WeakMem.Arch} {R1 : WakeA64.Cfg → TermRun.Cfg → Prop} {D : WakeW1.WSide {g : Gh // ok g}}
  {r0 r1 : {g : Gh // ok g} → Range}

/-- `WCompat0.lbl0`. -/
theorem lbl0_I : ∀ w, (wakeM hp i ok lab μT hoff).lbl w =
    ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).SR w).lbl := fun _ => rfl

/-- `WCompat0.K0`. -/
theorem K0_I : ∀ w, ((wakeM hp i ok lab μT hoff).ms w).K = some abi := fun _ => rfl

/-- `WCompat0.G0` (and `WCompat.G` for `D.ms := wakeMs hp i`). -/
theorem G0_I : ∀ w, ((wakeM hp i ok lab μT hoff).ms w).G =
    (wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).G w := fun _ => rfl

/-- `WCompat0.own0` (and `WCompat.own`). -/
theorem own0_I : ∀ w s, ((wakeM hp i ok lab μT hoff).ms w).own s = [] := fun _ _ => rfl

/-- `WakeAssembly`'s `hMμ`: main's side's marks are `μT` (at `μT :=` the
loaded program's marks, `rfl`). -/
theorem hMμ_I : (wakeM hp i ok lab μT hoff).μ = μT := rfl

/-- `WCompat0.live0`. -/
theorem live0_I : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c → c.term ≠ wlRet :=
  fun _ s c h => (mainInv_W s c h).1.2.1

/-- main's states are wide on the layout's executable (`WCompat0.wide0`,
`sysExec0`). -/
theorem wideX_I : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c →
    Spike.Lib.A64.WideKeep.WideX (RuntimeLayout.ofPlaceW hp i).exe s :=
  fun _ s c h => (mainInv_W s c h).1.2.2.1

/-- main's environment is placed at the spawn's placement (`hplM`). -/
theorem placed_I : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c →
    Spike.Lib.A64Consumer.Placed (RuntimeLayout.ofPlaceW hp i).Λ (wakeSR w.1).lbl s c :=
  fun _ s c h => (mainInv_W s c h).1.2.2.2

/-- `WCompat0.relW0`: main's instructions write at most once, a release
write. -/
theorem relW0_I : ∀ w s c e, (wakeM hp i ok lab μT hoff).Mi w s c → isaLSE2.exec s = some e →
    EvTree.RelW1 Arch.armv8 e :=
  fun _ s c _ h he => (mainInv_W s c h).2.1.2 _ he

/-- `WakeAssembly`'s `hhalt0`: main's states run (at a system call too). -/
theorem hhalt0_I : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c → abi.atSys s = true →
    (isaLSE2.exec s).isSome :=
  fun _ s c h _ => (mainInv_W s c h).2.1.1

/-- `WakeMappedRow.hM_of`'s `hlab`: main's label words are mapped in `K0`. -/
theorem labMapped_I : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c →
    Spike.Lib.WakeMappedRow.LabMapped ((wakeM hp i ok lab μT hoff).lbl w)
      (Spike.Lib.A64Consumer.K0 (RuntimeLayout.ofPlaceW hp i).Λ) c :=
  fun _ s c h => (mainInv_W s c h).2.2.1

/-- `WakeAssembly`'s `hmapM` (`WakeMappedRow.hM_of`): main's instructions
touch only locations mapped in `K0`. -/
theorem hmapM_I : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c → abi.atSys s = false →
    ∀ e, isaLSE2.exec s = some e →
      ¬ Scc.Sem.Kernel.Touches
        (fun l w => Scc.Sem.Kernel.mapped (K0 (RuntimeLayout.ofPlaceW hp i).Λ) w l = false) e :=
  Spike.Lib.WakeMappedRow.hM_of (fun _ => rfl) (fun _ _ _ h => h.1) (labMapped_I hp i)

/-- `WCompat0.noSite0` at the placed output's marks: main is at no transfer
site (`A64AbOffL.noSite_of_A_ofPlaceOK`), for `lab` the layout's labels. -/
theorem noSite0_I (hlab : lab = (RuntimeLayout.ofPlaceW hp i).lab) : ∀ w s c, (wakeM hp i ok lab μT hoff).Mi w s c →
    Scc.Sem.Kernel.siteAt abi (Spike.Lib.A64.PhRec.μ (RuntimeLayout.ofPlaceW hp i)) s = none := by
  subst hlab
  exact fun _ s c h => Spike.Lib.A64AbOffL.noSite_of_A_ofPlaceOK hp i (mainInv_W s c h).1.1

/-- `WCompat0.noWrite0`: main's system calls are `futex` or `exit_group`
(`MainSys`), never `write`. -/
theorem noWrite0_I : ∀ w s c fd buf n, (wakeM hp i ok lab μT hoff).Mi w s c → abi.atSys s = true →
    Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n) := by
  intro _ s c fd buf n h ha
  show Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 s.st.1.regs.X8.toNat _ ≠ _
  rcases (mainInv_W s c h).2.2.2.1 ha with h | h <;> rw [h] <;>
    simp [Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64] <;> repeat (first | split | simp)

/-- At `wlIf` in `mainInv`, `d` bound to a number other than `1` is
impossible (`FlagW`'s first fact). -/
theorem not_flagIf {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {lab : String → Int64}
    {exe : _root_.Executable} {Λ : Scc.Sem.Layout} {lsize : WeakMem.AllocLabel → Nat} {s : State}
    {env : TermRun.Env} {t : Ty} {n : Nat} (hn : n ≠ 1)
    (h : mainInv lbl ms (mainWR lab exe Λ lbl lsize) s
      ⟨WakeM0.wlIf, ("d", t, [TermRun.cst (.num n)]) :: env, none⟩) : False :=
  have h1 : n < 2 ^ 64 ∧ 1 = n :=
    (mainInv_W _ _ h).2.2.2.2.1 rfl t (TermRun.cst (.num n)) (by simp [TermRun.lookupE, List.find?])
  hn h1.2.symm

/-- `WCompat0.flagLd`: at `wlBody` main's only load of the flag's word is
`waitLoop`'s `ldar` (`OutL.load` or `OutL.ldSt`; every other row's event
differs, a system call faults, the address is the flag's, inside its label,
not the runtime's); a value other than `1` would land at `wlIf` with `d`
another number (`FlagW`'s first fact), and an `ldSt` at a value `V ≥ 2^64`
would stutter at `q` with `x9 = 1` (its third and fourth). -/
theorem flagLd_I : ∀ w s c (kl : Kraken.LoadKind) (A : BitVec 64) (k : Val → isaLSE2.State) (ty : Ty)
    (wd : TermRun.Word),
    (wakeM hp i ok lab μT hoff).Mi w s c → c.term = WakeM0.wlBody →
    isaLSE2.exec s = some (.load kl false ⟨A, 8⟩ fun v => .done (k v)) →
    TermRun.evalAt c.env (.var "c") = some (ty, [wd]) → ValRep ((wakeM hp i ok lab μT hoff).lbl w) wd.val A.toNat →
    (∀ v : Val, (v.setWidth 64).toNat ≠ 1 → (wakeM hp i ok lab μT hoff).Mi w (k v) c) ∧
    (∀ (v : Val) (w' : TermRun.Word), (v.setWidth 64).toNat = 1 → ((wakeM hp i ok lab μT hoff).ms w).rd w' →
      ValRep ((wakeM hp i ok lab μT hoff).lbl w) w'.val 1 →
      (wakeM hp i ok lab μT hoff).Mi w (k v) ⟨WakeM0.wlIf, ("d", loadTy ty, [w']) :: c.env, none⟩) := by
  intro w s c kl A k ty wd h hb he hev hv
  have hW := mainInv_W s c h
  have hvl : Kraken.Executable.ValidLayout s.exe := hW.1.2.2.1.2 ▸ (RuntimeLayout.ofPlaceW hp i).valid
  have hb' := hb
  unfold WakeM0.wlBody at hb'
  -- the load's continuation from another row's
  have hk : ∀ {kl' : Kraken.LoadKind} {A' : BitVec 64} {g : Val → State}, isaLSE2.exec s = some (.load kl' false ⟨A', 8⟩ fun v => .done (g v)) →
      A' = A ∧ ∀ v, g v = k v := by
    intro kl' A' g he'
    have hx := he'.symm.trans he
    simp only [Option.some.injEq, EvTree.load.injEq, Loc.mk.injEq, true_and, and_true] at hx
    exact ⟨hx.2.1, fun v => by injection congrFun hx.2.2 v⟩
  rcases mainInv_closed s c h with ⟨o⟩ | ⟨kl', A', g, x, a, e, ty', w0, V, he', ht, hev', -, hn, hy, -⟩
  · cases o with
    | silent _ _ he' => cases he'.symm.trans he
    | choice P t he' hs =>
      cases he'.symm.trans he
      exact hs.elim
    | load kl' A' g x a e ty' w0 he' ht hev' _ hx _ =>
      rw [hb'] at ht; cases ht
      rw [hev] at hev'; cases hev'
      obtain ⟨rfl, hgk⟩ := hk he'
      refine ⟨fun v hv1 => ?_, fun v w' _ hr hr' => hgk v ▸ hx v w' hr (by rwa [‹(v.setWidth 64).toNat = 1›])⟩
      exact (not_flagIf hv1 (hgk v ▸ hx v (TermRun.cst (.num (v.setWidth 64).toNat)) ⟨_, rfl⟩ ⟨BitVec.isLt _, rfl⟩)).elim
    | store _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | rtStore _ _ _ _ _ he' => cases he'.symm.trans he
    | rtLoad kl' L g c' he' hrt =>
      have hx := he'.symm.trans he
      simp only [Option.some.injEq, EvTree.load.injEq] at hx
      obtain ⟨-, -, rfl, -⟩ := hx
      obtain ⟨t, w1, sa, hl, hw, hs, hof⟩ := hW.2.2.2.2.2.1 hb
      have hof' : @LT.lt Nat _ sa.offset (w.1.lsize sa.label) := hof
      rw [show TermRun.evalAt c.env (.var "c") = TermRun.lookupE c.env "c" from rfl, hl] at hev
      cases hev
      rw [hw] at hv
      obtain ⟨-, x0, hx0, hA⟩ := hv
      obtain ⟨b, hbl⟩ := Option.isSome_iff_exists.mp hs
      have hx0' : (w.1.lbl sa.label).map (· + 8 * sa.offset) = some x0 := hx0
      rw [hbl, Option.map_some, Option.some.injEq] at hx0'
      have hx1 : @Eq Nat (b + 8 * sa.offset) x0 := hx0'
      have hA1 : A.toNat = x0 + 0 := hA
      refine (hrt ⟨sa.label, b, hbl, ?_⟩).elim
      show b ≤ A.toNat ∧ A.toNat < b + 8 * w.1.lsize sa.label
      omega
    | rtRmw _ _ _ _ _ he' => cases he'.symm.trans he
    | sys K _ hK ha =>
      cases Option.some.inj (hK.symm.trans (show (wakeMs hp i w.1).K = some abi from rfl))
      obtain ⟨_, hf⟩ := Spike.Lib.A64.SvcFault.exec_atSvc hvl ha he
      cases hf
    | holdLoad _ _ _ x sa u v e _ hX =>
      rcases hX.2 with ⟨_, _, _, _, ht, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, -⟩ <;> rw [hb'] at ht <;> cases ht
    | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | ctrRmw _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | alloc _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | newStore _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | emit K _ _ _ _ hK ha =>
      cases Option.some.inj (hK.symm.trans (show (wakeMs hp i w.1).K = some abi from rfl))
      obtain ⟨_, hf⟩ := Spike.Lib.A64.SvcFault.exec_atSvc hvl ha he
      cases hf
    | fence _ _ _ he' _ _ => cases he'.symm.trans he
  · rw [hb'] at ht; cases ht
    rw [hev] at hev'; cases hev'
    obtain ⟨rfl, hgk⟩ := hk he'
    obtain rfl : V = 1 := Classical.byContradiction fun hV => by
      by_cases hVl : V < 2 ^ 64
      · refine not_flagIf hV (hy (BitVec.ofNat 128 V) (TermRun.cst (.num V)) ?_ ⟨_, rfl⟩ ⟨hVl, rfl⟩)
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      · have h1 := hn 1 (by simp; omega)
        obtain ⟨s', hs', hq, h9⟩ := hW.2.2.2.2.2.2.1 hb _ _ A' _ _ hev hv he' 1
        cases hs'
        exact (mainInv_W _ _ h1).2.2.2.2.2.2.2 hb hq (by rw [h9]; rfl)
    exact ⟨fun v hv1 => hgk v ▸ hn v hv1, fun v w' h1 hr hr' => hgk v ▸ hy v w' h1 hr hr'⟩

/-- `WCompat0.mpW0`. -/
theorem mpW0_I :
    ∀ w L, ((wakeM hp i ok lab μT hoff).ms w).mp L true →
      ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).P w).foot 0 L ∧ ¬ InLabel ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).SR w).lbl ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).SR w).lsize L ∧
        Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared L := by
  intro w L h
  exact ⟨.inr (.inl h), (h.2 rfl).2, (h.2 rfl).1⟩

/-- `WCompat.mpW` for the worker's memory side `wakeMs hp i`. -/
theorem mpW_I :
    ∀ w : {g : Gh // ok g}, ∀ L, (wakeMs hp i w.1).mp L true →
      ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).P w).foot 1 L ∧ ¬ InLabel ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).SR w).lbl ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).SR w).lsize L ∧
        Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared L := by
  intro w L h
  exact ⟨.inr (.inl h), (h.2 rfl).2, (h.2 rfl).1⟩

/-- `WCompat.cTfoot`. -/
theorem cTfoot_I : ∀ w, ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).P w).foot 1
    ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).C w).cT :=
  fun _ => wakeP_foot_c

/-- `WCompat.cSfrz`. -/
theorem cSfrz_I : ∀ w, ¬ ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).P w).frzS
    ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).C w).cS :=
  fun _ => wakeP_not_frzS_c

/-- `WCompat.footLab`. -/
theorem footLab_I : ∀ w L, ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).P w).foot 1 L →
    InLabel ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).SR w).lbl
      ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).SR w).lsize L →
    L = ((wakeQI hp i ok arch R1 μT (wakeM hp i ok lab μT hoff) D r0 r1).C w).cT :=
  fun w _ hf hl => wakeP_footLab (wakeLocs_ok hp i w.1) hf hl

end Inst

/-- info: 'Spike.Lib.WakeInst.hrt8_of_limOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hrt8_of_limOk
/-- info: 'Spike.Lib.WakeInst.flagLd_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms flagLd_I

/-- info: 'Spike.Lib.WakeInst.rd_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rd_num

/-- info: 'Spike.Lib.WakeInst.footLab_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms footLab_I

end Spike.Lib.WakeInst
