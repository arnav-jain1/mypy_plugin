# Installation
Use uv to activate the venv
```bash
uv venv
source .venv/bin/activate
uv pip install -r requirements.txt
```

Running from command line: `mypy benchmarks\test3.py > output.txt` \
Running inside vscode: Should automatically work

The output.txt has the current outputs from running on test3.py

## Turning off flow sensitive
Comment out
```py
if ".func" in fullname:
    return self.custom_func
```


Tested with https://github.com/j0sephsasson/numpy-NN/blob/main/model/model.py