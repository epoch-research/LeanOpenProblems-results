class Type:
    def __init__(self, is_arrow=False, dom=None, cod=None, base=None):
        self.is_arrow = is_arrow
        self.dom = dom
        self.cod = cod
        self.base = base
    def __eq__(self, other):
        if not isinstance(other, Type): return False
        if self.is_arrow != other.is_arrow: return False
        if self.is_arrow:
            return self.dom == other.dom and self.cod == other.cod
        else:
            return self.base == other.base
    def __hash__(self):
        if self.is_arrow:
            return hash((True, self.dom, self.cod))
        else:
            return hash((False, self.base))
    def __str__(self):
        if self.is_arrow:
            return f"({self.dom} -> {self.cod})"
        else:
            return self.base

P = Type(base='PEmpty')
B = Type(is_arrow=True, dom=P, cod=P)
V1 = Type(is_arrow=True, dom=Type(is_arrow=True, dom=B, cod=P), cod=P)
V2 = Type(is_arrow=True, dom=Type(is_arrow=True, dom=V1, cod=P), cod=P)
V3 = Type(is_arrow=True, dom=Type(is_arrow=True, dom=V2, cod=P), cod=P)

def solve():
    env = [
        ("g", B),
        ("h1", V1),
        ("h2", V2),
        ("h3", V3)
    ]
    
    # We want to find a term of type P.
    # To do this efficiently, we can use a set of known terms, and iteratively apply them.
    # Also, we can introduce abstractions.
    # Since any abstraction of type X -> P is formed by assuming x:X and finding a term of type P,
    # we can represent this.
    # Let's keep a dict of: type -> set of (term_string)
    known = {}
    for name, typ in env:
        if typ not in known: known[typ] = set()
        known[typ].add(name)
        
    for step in range(1, 12):
        print(f"Step {step}...")
        # 1. Apply: if we have (f : X -> Y) and (x : X), we can form (f x : Y)
        new_terms = []
        for typ_f, terms_f in known.items():
            if typ_f.is_arrow:
                typ_x = typ_f.dom
                if typ_x in known:
                    for f_str in terms_f:
                        for x_str in known[typ_x]:
                            new_term = f"({f_str} {x_str})"
                            new_terms.append((new_term, typ_f.cod))
                            
        # 2. Abstract: if we want to form a term of type (X -> P), we can assume x:X and try to find a term of type P.
        # But we can only do this if we can construct a term of type P using x:X.
        # So we can temporarily add x:X to the environment and see if we can find P.
        # Let's do this for some common domains: B, V1, V2
        for dom in [B, V1, V2]:
            arrow_type = Type(is_arrow=True, dom=dom, cod=P)
            # Find if we can construct P with an extra variable of type dom
            var_name = f"var_{step}_{str(dom)[:3]}"
            # Temporary environment
            temp_known = {k: set(v) for k, v in known.items()}
            if dom not in temp_known: temp_known[dom] = set()
            temp_known[dom].add(var_name)
            
            # Run one-step applications in temp_known to see if we can get P
            for _ in range(3): # try up to 3 levels of application
                temp_new = []
                for tf, tfs in temp_known.items():
                    if tf.is_arrow and tf.dom in temp_known:
                        for f_str in tfs:
                            for x_str in temp_known[tf.dom]:
                                temp_new.append((f"({f_str} {x_str})", tf.cod))
                for t_str, t_typ in temp_new:
                    if t_typ not in temp_known: temp_known[t_typ] = set()
                    temp_known[t_typ].add(t_str)
                    
            if P in temp_known:
                for p_str in temp_known[P]:
                    if var_name in p_str: # must use the variable
                        new_term = f"(fun ({var_name} : {dom}) => {p_str})"
                        new_terms.append((new_term, arrow_type))
                        
        # Add new terms to known
        added = False
        for t_str, t_typ in new_terms:
            if t_typ not in known: known[t_typ] = set()
            if t_str not in known[t_typ]:
                known[t_typ].add(t_str)
                added = True
                
        if P in known:
            print("Found P:")
            for p_str in known[P]:
                print(p_str)
            return
            
        if not added:
            print("No new terms added, stopping.")
            break

solve()
