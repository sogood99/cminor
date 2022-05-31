#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# 使用方式：./test.py
# 这个脚本应该在你的验证工具的项目的根目录下运行

import os
import subprocess
import json

import timeit
from termcolor import colored

TIMEOUT=10 # 默认的超时时间是 10s

# 返回的是一个 (得分，总分) 的二元组
# 得分和总分都是直接是总评中的分数，不折分
def test():
    # 说明一下颜色的含义
    print("""
The color indicates your correctness:
  {} means your output is correct, aka, the same as the answer.
  {} means your ouput is UNKNOWN.
  {} means your output is incorrect, aka, at the opposite of the answer.
  {} means yours runs out of time or raises some error.

""".format(colored("Green", "green"), colored("Cyan", "cyan"), colored("Red", "red"), colored("Yellow", "yellow")))

    score_sum = 0
    total_score_sum = 0

    for category, total_score in [("partial_correctness", 21 * 0.8), ("total_correctness", 3 * 0.8)]:
        print("==========", category.upper(), "==========")

        # 初始化
        d = os.path.join(os.path.dirname(__file__), category)
        count = {
            "correct": 0,
            "unknown": 0,
            "timeout": 0,
            "error": 0,
            "incorrect": 0
        }

        # 跑起来！并且对输出进行检验
        def run_and_check(filepath: str, answer: str):
            try:
                cp = subprocess.run(["dotnet", "run", "-c", "Release", "--no-build", "--",
                                     "--source", filepath], check=True, capture_output=True, timeout=TIMEOUT)
            except subprocess.TimeoutExpired as e:
                # timeout 用黄色
                print(colored("TIMEOUT", "yellow"), end=' ')
                count["timeout"] = count["timeout"] + 1
                return
            except:
                # error 也用黄色
                print(colored("ERROR", "yellow"), end=' ')
                count["error"] = count["error"] + 1
                return

            # 如果一切正常，那么就来比较输出
            out = cp.stdout.decode("utf-8").strip()
            if out == "VERIFIED" or out.endswith("\nVERIFIED"):
                if answer == "VERIFIED":
                    # 答案正确用绿色
                    color = "green"
                    count["correct"] = count["correct"] + 1
                else:
                    # 答案错误用红色
                    assert answer == "UNVERIFIED"
                    color = "red"
                    count["incorrect"] = count["incorrect"] + 1
                print(colored("VERIFIED", color), end=' ')
            elif out == "UNVERIFIED" or out.endswith("\nUNVERIFIED"):
                if answer == "VERIFIED":
                    # 答案错误用红色
                    color = "red"
                    count["incorrect"] = count["incorrect"] + 1
                else:
                    # 答案正确用绿色
                    assert answer == "UNVERIFIED"
                    color = "green"
                    count["correct"] = count["correct"] + 1
                print(colored("UNVERIFIED", color), end=' ')
            else:
                # 以 UNKNOWN 或者其他奇奇怪怪的输出结尾的话，
                # 也都算作 UNKNOWN
                count["unknown"] = count["unknown"] + 1

                print(colored("UNKNOWN", "cyan"), end=' ')

        # 遍历每个 testcase
        with open(os.path.join(d, "answers.json"), "r") as f:
            testcases = json.load(f)
            for filename, answer in testcases.items():
                # 计算出 filepath 并检验其合法性
                filepath = os.path.join(d, filename)
                assert filepath.endswith(".c")
                assert os.path.exists(filepath)

                print(os.path.join(
                    category, filename) + " ", end="")

                # 无论结果如何，也要把消耗的时间打印出来
                time = timeit.timeit(
                    stmt='run_and_check(filepath, answer)',
                    globals=locals(),
                    number=1)
                print("{:.2f}s".format(time))

        # 计算最终的得分
        print("")
        print("{} testcases are correct.".format(count["correct"]))
        print("{} testcases unknow the reults.".format(count["unknown"]))
        print("{} testcases run out of time.".format(count["timeout"]))
        print("{} testcases report an error.".format(count["error"]))
        print("{} testcases are incorrect.".format(count["incorrect"]))
        print("")

        score = max((count["correct"] - 2 * count["incorrect"]
                     ) / sum(count.values()) * total_score, 0)
        print("You've got {:.2f} out of {:.2f} scores.".format(
            score, total_score))

        score_sum += score
        total_score_sum += total_score

        # 美观起见，我们再空一行
        print("")

    return (score_sum, total_score_sum)


if __name__ == "__main__":
    test()
