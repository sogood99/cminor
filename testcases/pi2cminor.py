import argparse
import json
import os

parser = argparse.ArgumentParser("Answer converter from .pi to .c")
parser.add_argument('--dir',
        type=str,
        help='the leaf directory of testcases.',
        required=True)

if __name__ == "__main__":
    args = parser.parse_args()

    # 把答案从 answers.json 中读出来
    pi_answers = {}
    with open(os.path.join(args.dir, 'answers.json'), 'r') as f:
        for x in json.load(f):
            pi_answers[x['filename']] = x['answer']

    # 从 pi_answers 转成 c_answers
    c_answers = {}
    for testcase in os.listdir(args.dir):
        if testcase.endswith('.c'):
            if testcase.replace('.c', '.pi') in pi_answers:
                c_answers[testcase] = pi_answers[testcase.replace('.c', '.pi')]
            else:
                print(f'new testcase: {testcase}')
    
    # 写回 answers.json
    with open(os.path.join(args.dir, 'answers.json'), 'w') as f:
        json.dump(c_answers, f, indent='\t')
