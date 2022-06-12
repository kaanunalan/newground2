def add_to_subdom(subdoms, var, value):
    """
    Adds the domains for variables and corresponding list of atoms to the dictionary of subdomains.

    :param subdoms: Dictionary of subdomains.
    :param var: Variable in the program.
    :param value: Symbolic or numeric constant.
    """
    if var.startswith("_dom_"):
        var = var[5:]
    else:
        return

    if var not in subdoms:
        subdoms[var] = []
        subdoms[var].append(value)
    elif value not in subdoms[var]:
        subdoms[var].append(value)
