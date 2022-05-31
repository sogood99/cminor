## 测例

这个是 CMinor 的验证工具的公开测例仓库。

所有的公开测例分为 partial correctness、total correctness 和 compilation 三大类，分别放在三个目录下面。其中 compilation 只是用于助教测试工具前端（将 CMinor 代码编译为控制流图），与后端的验证算法关系不大，你无需关心。

每个文件夹里有一个 `answers.json`，是这个文件夹里所有测例的答案，其格式如下

```json
[
    "filename": <answer>, // "VERIFIED" or "UNVERIFIED"
    ...
]
```

## 评测脚本

你可以对每个测例单独测试及调试，也可以使用我们提供的评测脚本。

需要 Python >= 3.8，并安装所需的包：

```bash
pip3 install -r requirements.txt
```

在验证工具的根目录下，使用：

```bash
dotnet build -c Release # 编译
python3 testcases/test.py # 统一评测所有测例
```

## 时间限制

对于每个测例，我们默认给出的时间限制是 10s。
