/-
**Image-independent x64 helpers for the bounded
certification proofs** (x64, program-independent).

The x64 `LiveCertBounded*` files read the dependencies of a cell off its
directive and, in the ticket locks' spin loop (`movl (owner),%ecx` /
`cmpl %eax,%ecx` / `jne spin`), compare loop states that differ only in
`%rcx` and the flags. None of this depends on the image, so it is stated here
once:

- `directive_of_codeAt` and the tactic `x64depsAt h i P [us]` (the
  dependencies of the cell at position `i` of the laid-out image `P`);
- `cmpX`, the flags `cmpl %eax,%ecx` computes, a function of the registers;
- `Core s0 s` (`s0` with `%rcx` and the flags replaced, at some pc) and
  `Core.ld_cmp`: a load of `v` into `%ecx` then `cmpl` from two `Core` states
  gives the same state;
- `instrViews_ld`, `instrViews_cmp`: the instruction views of those cells;
- `XclbNone` (no pending load exclusive in a configuration, any ISA),
  `xclbNone_init`, and `xclbNone_step` from a per-step preservation fact.

Used by `LiveCertBoundedTicket2X64`. The existing `LiveCertBoundedTicketX64` and
`LiveCertBoundedSpinCmpx` keep their local copies.
-/
import Kraken.Promising.LiveCertCut
import Kraken.Promising.LiveSpinStep
import Kraken.Promising.LiveSem
import Kraken.Promising.SLR.X64Trees

namespace Kraken.Promising.Live.CertCutX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Sem

/-! ## Dependencies of a cell -/

/-- The directive at the pc, read off `codeAt` (the x64 twin of
`CertBoundedSpinCas.directive_of_codeAt`). -/
theorem directive_of_codeAt {st : State} {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hcode : Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest) : st.directive = some d := by
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  unfold State.directive
  simp only at hcode ⊢
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
    unfold Kraken.Executable.codeAt
    congr 1, hcode]
  rfl

/-- **Read the dependencies of the cell at position `i` of the laid-out image
`P`**: `h : At st i` (with fields `exe` and `pc`); `us` unfold `P` to its
directive list. -/
macro "x64depsAt" h:ident i:num P:term:max "[" us:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := $P) (i := $i) (d := ($P)[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : ($P)[$i] = d at hc
  simp only [$us,*, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  have hdir := Kraken.Promising.Live.CertCutX64.directive_of_codeAt (by rw [($h).exe]; exact hc)
  show Kraken.Promising.X64.deps _ = _
  unfold Kraken.Promising.X64.deps
  rw [hdir]
  rfl))

/-! ## The spin loop: `movl …,%ecx` then `cmpl %eax,%ecx` -/

/-- The flags `cmpl %eax,%ecx` computes: a function of the registers only. -/
def cmpX (r : Reg64s) : StatusFlags :=
  StatusFlags.from_result (r.get (.low .rcx .W32) - r.get (.low .rax .W32))
    { cf := (((4294967296 - (r.get (.low .rax .W32)).toNat : Nat) : Int) + ((r.get (.low .rcx .W32)).toNat : Int)) %
          4294967296 != ((r.get (.low .rcx .W32)).toNat : Int) - ((r.get (.low .rax .W32)).toNat : Int),
      af := (((BitVec.take (r.get (.low .rcx .W32) - r.get (.low .rax .W32)) 4).toNat : Int) !=
          ((BitVec.take (r.get (.low .rcx .W32)) 4).toNat : Int) - ((BitVec.take (r.get (.low .rax .W32)) 4).toNat : Int)),
      of := ((r.get (.low .rcx .W32)).toInt - (r.get (.low .rax .W32)).toInt).bmod 4294967296 !=
          (r.get (.low .rcx .W32)).toInt - (r.get (.low .rax .W32)).toInt }

theorem set64_rcx_self (r : Reg64s) : r.set64 .rcx r.rcx.toBitVec = r := by
  simp [Reg64s.set64]

/-- The machine state of a loop state: `s0`'s with `%rcx` and the flags
replaced, at some pc. -/
def Core (s0 s : State) : Prop :=
  ∃ (x : BitVec 64) (f : StatusFlags) (pc : Int64),
    s = { s0 with st := ({ s0.st.1 with regs := s0.st.1.regs.set64 .rcx x, status := f }, pc) }

theorem Core.self (s0 : State) : Core s0 s0 :=
  ⟨s0.st.1.regs.rcx.toBitVec, s0.st.1.status, s0.st.2, by rw [set64_rcx_self]⟩

theorem Core.flags {s0 s : State} (h : Core s0 s) (g : StatusFlags) (pc' : Int64) :
    Core s0 { s with st := ({ s.st.1 with status := g }, pc') } := by
  obtain ⟨x, f, pc, rfl⟩ := h
  exact ⟨x, g, pc', rfl⟩

theorem Core.set4 {s0 s : State} (h : Core s0 s) (v : BitVec 64) (pc' : Int64) :
    Core s0 { s with st := ({ s.st.1 with regs := s.st.1.regs.set64 .rcx v }, pc') } := by
  obtain ⟨x, f, pc, rfl⟩ := h
  exact ⟨v, f, pc', by simp⟩

theorem Core.goto {s0 s : State} (h : Core s0 s) (pc' : Int64) : Core s0 { s with st := (s.st.1, pc') } := by
  obtain ⟨x, f, pc, rfl⟩ := h
  exact ⟨x, f, pc', rfl⟩

/-- The state after a load of `v` into `%rcx` then `cmpl %eax,%ecx` (to
`p6`). -/
abbrev ldCmp (s : State) (v : BitVec 64) (p6 : Int64) : State :=
  { s with st := ({ s.st.1 with regs := s.st.1.regs.set64 .rcx v,
                                status := cmpX (s.st.1.regs.set64 .rcx v) }, p6) }

/-- **The load of `v` then `cmpl` from two loop states**: the same state. -/
theorem Core.ld_cmp {s0 s s' : State} (h : Core s0 s) (h' : Core s0 s') (v : BitVec 64) (p6 : Int64) :
    ldCmp s v p6 = ldCmp s' v p6 := by
  obtain ⟨x, f, pc, rfl⟩ := h
  obtain ⟨x', f', pc', rfl⟩ := h'
  simp

theorem instrViews_ld (t : Thread isa) :
    instrViews t { loadDefs := [.r .rcx] } = { addrR := 0, addrW := 0, dataR := 0, dataW := 0, condW := 0 } :=
  rfl

theorem instrViews_cmp (t : Thread isa) :
    instrViews t { dataRegs := [.r .rcx, .r .rax], defs := [.rflags] } =
      { addrR := 0, addrW := 0, dataR := max (max 0 (t.rview[2]! : View)) t.rview[0]!,
        dataW := max (max 0 (t.wview[2]! : View)) t.wview[0]!, condW := 0 } := rfl

/-! ## No pending load exclusive -/

section Xclb

variable {I : ISA}

/-- No thread has a pending load exclusive. -/
def XclbNone (cfg : Config I) : Prop := ∀ (i : Nat) u, cfg.threads[i]? = some u → u.views.xclb = none

theorem xclbNone_init (states : List I.State) (initMem : List (Loc × Val)) :
    XclbNone (Config.init states initMem) := by
  intro i u hu
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
  obtain ⟨s, -, rfl⟩ := hu
  rfl

/-- `XclbNone` across a semantic step whose instruction steps keep
`xclb = none` (promise steps leave it alone). -/
theorem xclbNone_step {A : Arch} {fuel tid : Nat} {cfg cfg' : Config I} (h : XclbNone cfg)
    (hpres : ∀ t outs (oc : Outcome I), cfg.threads[tid]? = some t → stepOne A t tid cfg.mem = some outs →
      .ok oc ∈ outs → t.views.xclb = none → oc.thread.views.xclb = none)
    (hst : StepSem A fuel tid cfg cfg') : XclbNone cfg' := by
  rcases hst with ⟨t, outs, oc, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · intro i u hu
    rcases SpinStep.wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact hpres t outs oc ht hs ho (h _ t ht)
    · exact h i u hu
  · intro i u hu
    rcases SpinStep.wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact h _ t ht
    · exact h i u hu

end Xclb

end Kraken.Promising.Live.CertCutX64
