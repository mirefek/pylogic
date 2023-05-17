from weakref import WeakValueDictionary
from term import Term, TermApp, BVar

def term_to_instr_list_aux(term, cache, res_list):
    res = cache.get(term, None)
    if res is not None: return res
    if isinstance(term, BVar):
        value = (term.debruijn_height,)
    else:
        value = (term.f,)+tuple(
            term_to_instr_list_aux(arg, cache, res_list)
            for arg in term.args
        )
    res = cache.get(value, None)
    if res is not None:
        cache[term] = res
        return res
    res = len(res_list)
    cache[term] = res
    cache[value] = res
    res_list.append((value, term))
    return res

def term_to_instr_list(term): # can be used as a key
    res = []
    res_i = term_to_instr_list_aux(term, dict(), res)
    assert res_i == len(res)-1
    instr_list = tuple(value for value, t in res)
    terms = [t for value, t in res]
    return instr_list, terms

class TermCache:
    def __init__(self):
        self._term_to_res = WeakValueDictionary()
        self._f_args_res = WeakValueDictionary()
        self._bvar_to_res = WeakValueDictionary()

    def share(self, term):
        res = self._term_to_res.get(term, None)
        if res is not None: return res
        if isinstance(term, BVar):
            res = self._bvar_to_res.setdefault(term.debruijn_height, term)
        else:
            args = tuple(
                self.share(arg) for arg in term.args
            )
            res = self._f_args_res.get((term.f, args), None)
            if res is None:
                if args == term.args: res = term
                else:
                    res = TermApp(term.f, args, term.bound_names)
                    self._term_to_res[res] = res
                self._f_args_res[term.f, args] = res

        self._term_to_res[term] = res
        return res
