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
W = Type(base='W')
Y = Type(is_arrow=True, dom=W, cod=P)
V3 = Type(is_arrow=True, dom=Type(is_arrow=True, dom=Y, cod=P), cod=P)
V2 = Type(is_arrow=True, dom=Type(is_arrow=True, dom=V3, cod=P), cod=P)
V1 = Type(is_arrow=True, dom=Type(is_arrow=True, dom=V2, cod=P), cod=P)
V0 = Type(is_arrow=True, dom=Type(is_arrow=True, dom=V1, cod=P), cod=P)

def solve():
    env = [
        ("g3", Y),
        ("h3", V3),
        ("h2", V2),
        ("h1", V1),
        ("h0", V0)
    ]
    
    known = {}
    for name, typ in env:
        if typ not in known: known[typ] = set()
        known[typ].add(name)
        
    for step in range(1, 15):
        print(f"Step {step}...")
        new_terms = []
        
        # 1. Apply: f : X -> Y and x : X => f x : Y
        for typ_f, terms_f in list(known.items()):
            if typ_f.is_arrow:
                typ_x = typ_f.dom
                if typ_x in known:
                    for f_str in terms_f:
                        for x_str in known[typ_x]:
                            new_term = f"({f_str} {x_str})"
                            new_terms.append((new_term, typ_f.cod))
                            
        # 2. Abstract: assume var : Dom, try to find P
        # Dom can be any of Y->P, V3->P, V2->P, V1->P, W
        domains = [V0, V1, V2, V3, Y, W]
        
        for dom in domains:
            arrow_type = Type(is_arrow=True, dom=dom, cod=P)
            var_name = f"v_{step}_{str(dom)[:3].replace('(', '').replace(' ', '')}"
            
            temp_known = {k: set(v) for k, v in known.items()}
            if dom not in temp_known: temp_known[dom] = set()
            temp_known[dom].add(var_name)
            
            # Simple application search in temp
            for _ in range(4):
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
                    if var_name in p_str:
                        new_term = f"(fun ({var_name} : {dom}) => {p_str})"
                        new_terms.append((new_term, arrow_type))
                        
        added = False
        for t_str, t_typ in new_terms:
            if t_typ not in known: known[t_typ] = set()
            if t_str not in known[t_typ]:
                known[t_typ].add(t_str)
                print(f"Added {t_str} of type {t_typ}")
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
