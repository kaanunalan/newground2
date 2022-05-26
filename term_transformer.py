import re

from clingo.ast import Transformer

from add_subdom import add_to_subdom


class TermTransformer(Transformer):
    def __init__(self, subdoms, no_show=False):
        self.__terms = []
        self.__subdoms = subdoms
        self.__facts = {}
        self.__ng_heads = {}
        self.__ng = False
        self.__show = False
        self.__shows = {}
        self.__current_f = None
        self.__no_show = no_show

    def visit_Rule(self, node):
        # Visits and transforms the children of the given AST
        # Necessary for programs without instantiated domains
        self.visit_children(node)
        # Get rule head predicate name
        pred = str(node.head).split("(", 1)[0]
        # Get list of arguments of the rule head
        arguments = re.sub(r"^.*?\(", "", str(node.head))[:-1].split(",")
        # Get arity (length of arguments) of predicate
        arity = len(arguments)

        # If program non-ground, save pred and arity (except #false) for later use
        if self.__ng:
            self.__ng = False
            if str(node.head) != "#false":
                # save pred and arity for later use
                if pred not in self.__ng_heads:
                    self.__ng_heads[pred] = {arity}
                else:
                    self.__ng_heads[pred].add(arity)
        # Add to facts if body length is zero
        elif node.body.__len__() == 0:
            arguments = ",".join(arguments)
            if pred not in self.__facts:
                self.__facts[pred] = {}
                self.__facts[pred][arity] = {arguments}
            elif arity not in self.__facts[pred]:
                self.__facts[pred][arity] = {arguments}
            else:
                self.__facts[pred][arity].add(arguments)
        return node

    def visit_Function(self, node):
        self.__current_f = str(node).split("(", 1)[0] if len(node.arguments) > 0 else node
        # shows
        # if not str(node.name).startswith('_dom_'):
        if node.name in self.__shows:
            self.__shows[node.name].add(len(node.arguments))
        else:
            self.__shows[node.name] = {len(node.arguments)}
        # Visits and transforms the children of the given AST
        # Necessary for programs without instantiated domains
        self.visit_children(node)
        return node

    def visit_Variable(self, node):
        self.__ng = True
        return node

    def visit_Interval(self, node):
        for i in range(int(str(node.left)), int(str(node.right))+1):
            if str(i) not in self.__terms:
                self.__terms.append(str(i))
            add_to_subdom(self.__subdoms, self.__current_f, str(i))
        return node

    def visit_SymbolicTerm(self, node):
        if str(node) not in self.__terms:
            self.__terms.append(str(node))
        add_to_subdom(self.__subdoms, self.__current_f, str(node))
        return node

    def visit_ShowSignature(self, node):
        self.__show = True
        if not self.__no_show:
            print(node)
        return node

    def get_terms(self):
        return self.__terms

    def get_subdoms(self):
        return self.__subdoms

    def get_facts(self):
        return self.__facts

    def get_ng_heads(self):
        return self.__ng_heads

    def get_shows(self):
        return self.__shows

    def get_show(self):
        return self.__show

    terms = property(get_terms)
    subdoms = property(get_subdoms)
    facts = property(get_facts)
    ng_heads = property(get_ng_heads)
    shows = property(get_shows)
    show = property(get_show)


