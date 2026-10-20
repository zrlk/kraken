#!/usr/bin/env python3
"""Generate the Michael-Scott queue .kl examples (unrolled enqueues/dequeues)."""
import sys

HEADER_OK = """AArch64 {name}
(* Michael-Scott queue (Promising-ARM PLDI'19 §7 "QU"), {desc}
   Static nodes: `d` is the initial dummy (head = tail = d), `n1`, `n2` are
   the enqueued nodes; node data at [n], next pointer at [n,#8].
   Enqueue: STR data; loop {{ LDAR tail; LDAR tail.next; if next != 0 then
   {linkop} tail -> next, retry; {linkop} tail.next: 0 -> node; }}; {linkop}
   tail -> node. Dequeue (retried until non-empty): LDAR head; LDAR tail;
   LDAR head.next; if head = tail then (empty or help advance tail) else
   LDR next.data; {linkop} head -> next.
   {prop}
   Expected: {expect}. (Threads have different roles: do not use -sym.) *)
# flags:
# expect: {expect}
"""

def enq(i, node_reg, val, linkop):
    return f"""enq{i}:
  MOV X2,{node_reg}
  MOV W9,#{val}
  STR W9,[X2]
enq{i}_loop:
  LDAR X3,[X1]
  ADD X8,X3,#8
  LDAR X4,[X8]
  CBNZ X4,enq{i}_fix
  MOV X5,#0
  {linkop} X5,X2,[X8]
  CBNZ X5,enq{i}_loop
  MOV X5,X3
  {linkop} X5,X2,[X1]
  B enq{i}_end
enq{i}_fix:
  MOV X5,X3
  {linkop} X5,X4,[X1]
  B enq{i}_loop
enq{i}_end:
"""

def deq(i, res_reg, linkop):
    return f"""deq{i}:
  LDAR X3,[X0]
  LDAR X4,[X1]
  ADD X8,X3,#8
  LDAR X5,[X8]
  CMP X3,X4
  B.NE deq{i}_ne
  CBZ X5,deq{i}
  MOV X6,X3
  {linkop} X6,X5,[X1]
  B deq{i}
deq{i}_ne:
  CBZ X5,deq{i}
  LDR W7,[X5]
  MOV X6,X3
  {linkop} X6,X5,[X0]
  CMP X6,X3
  B.NE deq{i}
  MOV W{res_reg},W7
"""

def gen(name, ndeq, linkop, expect, desc, prop, cond, nenq=2, ndeqops=2, slow=False):
    out = HEADER_OK.format(name=name, desc=desc, linkop=linkop, prop=prop, expect=expect)
    if slow:
        out = out.replace("# flags:\n", "# flags:\n# slow\n")
    if expect == "Sometimes":
        # Status line (Litmus/KNOWN_GAPS.md): the reachability theorem.
        snake = name.lower().replace("relaxed", "_relaxed")  # MSQueueRelaxed1 -> msqueue_relaxed1
        camel = "".join(w[:1].upper() + w[1:] for w in snake.split("_"))
        out = out.replace("# expect: Sometimes\n", "# expect: Sometimes\n# Proved reachable: "
                          f"Kraken.Promising.Reach.{camel}.{snake}_reachable "
                          f"(Kraken/Promising/ReachA64{camel}.lean)\n")
    inits = ["head=d; tail=d; d=0; n1=0; n2=0;",
             "0:X0=head; 0:X1=tail; 0:X12=n1; 0:X13=n2;"]
    threads = ["P0: enq pdone"]
    for t in range(1, ndeq + 1):
        inits.append(f"{t}:X0=head; {t}:X1=tail;")
        threads.append(f"P{t}: deq{t} ddone{t}")
    out += "{\n" + "\n".join(inits) + "\n}\n"
    out += "threads { " + "; ".join(threads) + "; }\n"
    out += "code {\nenq:\n"
    out += enq(1, "X12", 1, linkop)
    if nenq == 2:
        out += enq(2, "X13", 2, linkop)
    out += "  B pdone\npdone:\n  NOP\n"
    if ndeq == 1:
        # one dequeuer, `ndeqops` dequeues in order
        out += "deq1:\n" + deq("1a", 10, linkop)
        if ndeqops == 2:
            out += deq("1b", 11, linkop)
        out += "  B ddone1\nddone1:\n  NOP\n"
    else:
        for t in range(1, ndeq + 1):
            out += f"deq{t}:\n" + deq(f"{t}a", 10, linkop) + f"  B ddone{t}\nddone{t}:\n  NOP\n"
    out += "}\n" + cond + "\n"
    return out

files = {
  "msqueue2.kl": gen("MSQueue2", 1, "CASAL", "Always",
      "compiler-style annotations (CASAL on\n   tail.next, tail and head): one enqueuer of values 1,2 and one dequeuer\n   that dequeues twice into X10, X11.",
      "Property: the dequeuer receives 1 then 2 (FIFO, nothing lost, nothing\n   duplicated, data visible).",
      "forall (1:X10=1 /\\ 1:X11=2)"),
  "msqueue3.kl": gen("MSQueue3", 2, "CASAL", "Always",
      "compiler-style annotations (CASAL on\n   tail.next, tail and head): one enqueuer of values 1,2 and two dequeuers\n   each dequeuing once into X10.",
      "Property: the two dequeuers receive 1 and 2, one each (nothing lost,\n   nothing duplicated, data visible).",
      "forall ((1:X10=1 /\\ 2:X10=2) \\/ (1:X10=2 /\\ 2:X10=1))", slow=True),
  "msqueue_relaxed2.kl": gen("MSQueueRelaxed2", 1, "CAS", "Sometimes",
      "relaxed variant: plain CAS (no\n   release) on tail.next, tail and head, so the node's data STR is not\n   ordered before the link and the dequeuer can read stale data (0).\n   One enqueuer of values 1,2 and one dequeuer that dequeues twice.",
      "Property checked: the dequeuer receives 1 then 2 (forall).",
      "forall (1:X10=1 /\\ 1:X11=2)", slow=True),
  "msqueue1.kl": gen("MSQueue1", 1, "CASAL", "Always",
      "compiler-style annotations (CASAL on\n   tail.next, tail and head): one enqueuer of value 1 and one dequeuer\n   that dequeues once into X10 (smallest instance).",
      "Property: the dequeuer receives 1 (nothing lost, data visible).",
      "forall (1:X10=1)", nenq=1, ndeqops=1),
  "msqueue_relaxed1.kl": gen("MSQueueRelaxed1", 1, "CAS", "Sometimes",
      "relaxed variant: plain CAS (no\n   release) on tail.next, tail and head, so the node's data STR is not\n   ordered before the link and the dequeuer can read stale data (0).\n   One enqueuer of value 1 and one dequeuer that dequeues once (smallest\n   instance).",
      "Property checked: the dequeuer receives 1 (forall).",
      "forall (1:X10=1)", nenq=1, ndeqops=1),
}
import os
d = os.path.dirname(os.path.abspath(__file__))
for f, s in files.items():
    open(os.path.join(d, f), "w").write(s)
    print("wrote", f)
