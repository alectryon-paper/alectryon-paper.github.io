from pprint import pprint
from json import dump
from alectryon.core import SerAPI
from alectryon.json import minimal_json_of_annotated
with SerAPI() as api:
    r = api.run("Let inv b: negb (negb b) = b.\n"
                "  destruct b. all: reflexivity.\n"
                "Qed.\n"
                "Print Assumptions inv.")
    with open("api.pp", mode="w") as pp:
        pprint(r, stream=pp)
    with open("api.json", mode="w") as js:
        dump(minimal_json_of_annotated(r), js, indent=2)
