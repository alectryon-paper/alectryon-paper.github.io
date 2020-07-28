#!/usr/bin/env python3

# import sys
# from os.path import realpath
# sys.path.insert(0, realpath("../../"))

import alectryon.core, alectryon.cli
alectryon.core.SerAPI.DEFAULT_PP_ARGS['pp_margin'] = 50
alectryon.cli.main()
