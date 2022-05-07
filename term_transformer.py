import re

from clingo.ast import Transformer

from add_subdom import add_to_subdom


class TermTransformer(Transformer):
    def __init__(self, sub_doms, no_show=False):
        self.terms = []
        self.sub_doms = sub_doms
        self.facts = {}
        self.ng_heads = {}
        self.ng = False
        self.show = False
        self.shows = {}
        self.current_f = None
        self.no_show = no_show

    def visit_Rule(self, node):
        self.visit_children(node)
        pred = str(node.head).split('(', 1)[0]
        arguments = re.sub(r'^.*?\(', '', str(node.head))[:-1].split(',')
        arity = len(arguments)

        if self.ng:
            self.ng = False
            if str(node.head) != "#false":
                # save pred and arity for later use
                if pred not in self.ng_heads:
                    self.ng_heads[pred] = {arity}
                else:
                    self.ng_heads[pred].add(arity)
        elif node.body.__len__() == 0:
            arguments = ','.join(arguments)
            if pred not in self.facts:
                self.facts[pred] = {}
                self.facts[pred][arity] = {arguments}
            elif arity not in self.facts[pred]:
                self.facts[pred][arity] = {arguments}
            else:
                self.facts[pred][arity].add(arguments)
        return node

    def visit_Function(self, node):
        self.current_f = str(node).split("(", 1)[0] if len(node.arguments) > 0 else node
        # shows
        #if not str(node.name).startswith('_dom_'):
        if node.name in self.shows:
            self.shows[node.name].add(len(node.arguments))
        else:
            self.shows[node.name] = {len(node.arguments)}
        self.visit_children(node)
        return node

    def visit_Variable(self, node):
        self.ng = True
        return node

    def visit_Interval(self, node):
        for i in range(int(str(node.left)), int(str(node.right))+1):
            if (str(i) not in self.terms):
                self.terms.append(str(i))
            add_to_subdom(self.sub_doms, self.current_f, str(i))
        return node

    def visit_SymbolicTerm(self, node):
        if (str(node) not in self.terms):
            self.terms.append(str(node))
        add_to_subdom(self.sub_doms, self.current_f, str(node))
        return node

    def visit_ShowSignature(self, node):
        self.show = True
        if not self.no_show:
            print (node)
        return node
