#!/usr/bin/env python3
"""Cross two or more leanexport NDJSON documents into one.

Each input is a self-contained export with positional `in`/`il`/`ie` tables.
The merge remaps every index in document k by a disjoint offset so the
concatenated record stream still binds every reference before use.

Declaration names are resolved semantically (Name.anonymous = index 0) and
deduplicated across inputs: the first document wins, later declarations of an
already-declared name are dropped. Table records are never deduplicated —
duplicate structural names/levels/exprs are harmless.

Usage: cross.py OUT.ndjson IN1.ndjson IN2.ndjson [IN3...]
"""

import json
import sys

# index-space of every value, keyed by JSON object key
IN_KEYS = {"name", "pre", "induct", "typeName", "ctor", "param"}
IN_LIST_KEYS = {"all", "ctors", "levelParams"}
IL_KEYS = {"succ", "sort"}
IL_LIST_KEYS = {"max", "imax", "us"}
IE_KEYS = {"type", "value", "body", "fn", "arg", "struct", "expr", "rhs"}


def load(path):
    recs = []
    for line in open(path):
        line = line.strip()
        if line:
            recs.append(json.loads(line))
    return recs


class Merger:
    def __init__(self):
        self.in_base = 1  # index 0 is implicit Name.anonymous
        self.il_base = 1  # index 0 is implicit Level.zero
        self.ie_base = 0  # ie has no implicit entry; files start at 0 or 1
        self.in_map = {}   # per-file maps, rebuilt each file
        self.il_map = {}
        self.ie_map = {}
        self.in_defs = {}  # new idx -> record (for name resolution)
        self.declared = set()
        self.out = []
        self.dropped = []

    def remap_in(self, i):
        if i == 0:
            return 0
        return self.in_map[i]

    def remap_il(self, i):
        if i == 0:
            return 0
        return self.il_map[i]

    def remap_ie(self, i):
        return self.ie_map[i]

    def remap_list(self, v, fn):
        if v and all(isinstance(x, int) for x in v):
            return [fn(x) for x in v]
        return [self.remap_obj(x) for x in v]

    def remap_obj(self, obj):
        if isinstance(obj, dict):
            out = {}
            for k, v in obj.items():
                if k in IN_KEYS:
                    out[k] = self.remap_in(v)
                elif k in IN_LIST_KEYS:
                    out[k] = self.remap_list(v, self.remap_in)
                elif k in IL_KEYS:
                    out[k] = self.remap_il(v)
                elif k in IL_LIST_KEYS:
                    out[k] = self.remap_list(v, self.remap_il)
                elif k in IE_KEYS:
                    out[k] = self.remap_ie(v)
                else:
                    out[k] = self.remap_obj(v)
            return out
        if isinstance(obj, list):
            return [self.remap_obj(x) for x in obj]
        return obj

    def resolve_name(self, idx):
        parts = []
        while idx != 0:
            rec = self.in_defs[idx]
            if "str" in rec:
                parts.append(rec["str"]["str"])
                idx = rec["str"]["pre"]
            elif "num" in rec:
                parts.append(str(rec["num"]["i"]))
                idx = rec["num"]["pre"]
            else:
                raise ValueError(f"bad in record at {idx}: {rec}")
        return ".".join(reversed(parts))

    def decl_names(self, rec):
        """Semantic names a declaration record binds."""
        if "inductive" in rec:
            ind = rec["inductive"]
            names = set()
            for t in ind.get("types", []):
                names.add(self.resolve_name(t["name"]))
            for c in ind.get("ctors", []):
                names.add(self.resolve_name(c["name"]))
            for r in ind.get("recs", []):
                names.add(self.resolve_name(r["name"]))
            return names
        for k in ("def", "thm", "axiom", "opaque", "quot"):
            if k in rec:
                return {self.resolve_name(rec[k]["name"])}
        return set()

    def merge_file(self, recs, is_first):
        self.in_map, self.il_map, self.ie_map = {}, {}, {}
        next_in, next_il, next_ie = self.in_base, self.il_base, self.ie_base
        # pass 1: assign new table indices (order-preserving)
        for rec in recs:
            if "in" in rec and isinstance(rec.get("in"), int):
                self.in_map[rec["in"]] = next_in
                next_in += 1
            elif "il" in rec:
                self.il_map[rec["il"]] = next_il
                next_il += 1
            elif "ie" in rec:
                self.ie_map[rec["ie"]] = next_ie
                next_ie += 1
        # pass 2: emit remapped records, dedup declarations
        for rec in recs:
            if "meta" in rec:
                if is_first:
                    self.out.append(rec)
                continue
            if "in" in rec and isinstance(rec.get("in"), int):
                nr = self.remap_obj(rec)
                nr["in"] = self.in_map[rec["in"]]
                self.in_defs[nr["in"]] = nr
                self.out.append(nr)
            elif "il" in rec:
                nr = self.remap_obj(rec)
                nr["il"] = self.il_map[rec["il"]]
                self.out.append(nr)
            elif "ie" in rec:
                nr = self.remap_obj(rec)
                nr["ie"] = self.ie_map[rec["ie"]]
                self.out.append(nr)
            else:
                nr = self.remap_obj(rec)
                names = self.decl_names(nr)
                if names & self.declared:
                    self.dropped.append(sorted(names & self.declared))
                    continue
                self.declared |= names
                self.out.append(nr)
        self.in_base, self.il_base, self.ie_base = next_in, next_il, next_ie


def main():
    out_path = sys.argv[1]
    ins = sys.argv[2:]
    m = Merger()
    for i, p in enumerate(ins):
        m.merge_file(load(p), is_first=(i == 0))
    with open(out_path, "w") as f:
        for rec in m.out:
            f.write(json.dumps(rec, separators=(",", ":")) + "\n")
    print(f"{out_path}: {len(m.out)} records, {len(m.declared)} decls, "
          f"{len(m.dropped)} dropped (dup names: "
          f"{sum(len(d) for d in m.dropped)})")


if __name__ == "__main__":
    main()
