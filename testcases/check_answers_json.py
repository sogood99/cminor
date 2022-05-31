import os
import json
from termcolor import colored

category = ['partial_correctness', 'total_correctness']

for cat in category:
  p = os.path.join(os.path.dirname(__file__), cat)

  with open(os.path.join(p, 'answers.json')) as f:
    j = json.load(f)
    filename_in_json = j.keys()
    filename_in_dir = set(filter(lambda x: x[-3:] == '.pi', os.listdir(p)))
    
    if filename_in_dir != filename_in_json:
      print('files listed in', os.path.join(p, 'answers.json'), 'are', 
        colored('not identical', 'red'), 'to those in the folder')
      difs = filename_in_json.symmetric_difference(filename_in_dir)
      for dif in difs:
        if dif in filename_in_dir and dif not in filename_in_json:
          print('>', dif, colored('in the directory, but not listed in answers.json', 'red'))
        else:
          print('>', dif, colored('in answers.json, but not in the directory', 'red'))
    else:
      print(os.path.join(p, 'answers.json'), colored('identical', 'green'))