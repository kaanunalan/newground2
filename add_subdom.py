def add_to_subdom(subdoms, var, value):
    """
    Add the domains for variables and corresponding list of atoms to the dictionary of subdomains

    :param subdoms: a dictionary of subdomains
    :param var: a variable
    :param value: a symbolic or numeric constant
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
