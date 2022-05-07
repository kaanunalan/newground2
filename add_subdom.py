def add_to_subdom(subdoms, var, value):
    if var.startswith("_dom_"):
        var = var[5:]
    else:
        return

    if var not in subdoms:
        subdoms[var] = []
        subdoms[var].append(value)
    elif value not in subdoms[var]:
        subdoms[var].append(value)
