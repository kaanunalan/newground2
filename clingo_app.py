import re

from clingo.ast import parse_files, parse_string, ProgramBuilder
from clingo.control import Control
from clingox.program import Program, ProgramObserver

from add_subdom import add_to_subdom
from nglp_transformer import NglpDlpTransformer
from term_transformer import TermTransformer


class ClingoApp(object):
    def __init__(self, name, no_show=False, ground_guess=False, ground=False):
        self.program_name = name
        self.sub_doms = {}
        self.no_show = no_show
        self.ground_guess = ground_guess
        self.ground = ground

        self.prg = Program()

    def main(self, ctl, files):
        ctl_insts = Control()
        ctl_insts.register_observer(ProgramObserver(self.prg))
        # read subdomains in #program insts.
        self._readSubDoms(ctl_insts,files)
        if self.ground:
            print(self.prg)

        term_transformer = TermTransformer(self.sub_doms, self.no_show)
        parse_files(files, lambda stm: term_transformer(stm))

        with ProgramBuilder(ctl) as bld:
            transformer = NglpDlpTransformer(bld, term_transformer.terms, term_transformer.facts, term_transformer.ng_heads, term_transformer.shows, term_transformer.sub_doms, self.ground_guess, self.ground)
            parse_files(files, lambda stm: bld.add(transformer(stm)))
            if transformer.counter > 0:
                parse_string(":- not sat.", lambda stm: bld.add(stm))
                print (":- not sat.")
                #parse_string(f"sat :- {','.join([f'sat_r{i}' for i in range(1, transformer.counter+1)])}.", lambda stm: self.bld.add(stm))
                print(f"sat :- {','.join([f'sat_r{i}' for i in range(1, transformer.counter+1)])}.")

                for p in transformer.f:
                    for arity in transformer.f[p]:
                        for c in transformer.f[p][arity]:
                            rule_sets = []
                            for r in transformer.f[p][arity][c]:
                                sum_sets = []
                                for subset in transformer.f[p][arity][c][r]:
                                    # print ([c[int(i)] for i in subset])
                                    sum_sets.append(f"1:r{r}_unfound{'_'+''.join(subset) if len(subset) < arity else ''}" + (f"({','.join([c[int(i)] for i in subset])})" if len(subset)>0 else ""))
                                sum_atom = f"#sum {{{'; '.join(sum_sets)}}} >= 1"
                                rule_sets.append(sum_atom)
                            head = ','.join(c)
                            print(f":- {', '.join([f'{p}' +(f'({head})' if len(head)>0 else '')] + rule_sets)}.")

                if not self.ground_guess:
                    for t in transformer.terms:
                        print (f"dom({t}).")

                if not self.no_show:
                    if not term_transformer.show:
                        for f in transformer.shows.keys():
                            for l in transformer.shows[f]:
                                print (f"#show {f}/{l}.")

    def _readSubDoms(self, ctl_insts, files):
        #ctl_insts = Control()
        for f in files:
            ctl_insts.load(f)
        ctl_insts.ground([("base", []), ("insts", [])])
        for k in ctl_insts.symbolic_atoms:
            if(str(k.symbol).startswith('_dom_')):
                var = str(k.symbol).split("(", 1)[0]
                atom = re.sub(r'^.*?\(', '', str(k.symbol))[:-1]
                add_to_subdom(self.sub_doms, var, atom)