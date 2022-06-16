/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System.IO;
using System.Collections.Generic;

namespace cminor
{
    using BasicPath = LinkedList<Block>;

    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public int Apply(IRMain cfg)
        {
            foreach (Function f in cfg.functions)
            {
                int retVal = checkedFunc(f);
                if (retVal == 0)
                {
                    return 0;
                }
                else if (retVal < 0)
                {
                    return -1;
                }
            }
            return 1;
        }

        // returns true if function passes check
        private int checkedFunc(Function f)
        {
            if (f.blocks.Count == 0)
            {
                return 0;
            }
            HashSet<Block> accessed = new HashSet<Block>(); // check if a block has been accessed
            LinkedList<BasicPath> basicPaths = new LinkedList<BasicPath>(); // all basic paths used in bfs

            // init basicPaths
            basicPaths.AddLast(new BasicPath(new Block[] { f.preconditionBlock }));
            // init accessed
            accessed.Add(f.preconditionBlock);

            while (basicPaths.Count != 0)
            {
                // breadth first search to find basic paths
                for (int i = 0; i < basicPaths.Count; i++)
                {
                    if (basicPaths.First is null)
                    {
                        // unknown error, basic paths should have Count number of paths
                        throw new System.Exception("Bug, number of basicPaths should have count > Count");
                    }

                    BasicPath p = basicPaths.First.Value;
                    basicPaths.RemoveFirst();

                    if (p.Last is null)
                    {
                        // unknown error, each path should be nonempty
                        throw new System.Exception("Bug, each basic path should be nonnull");
                    }

                    foreach (Block succBlk in p.Last.Value.successors)
                    {
                        BasicPath newPath = new BasicPath(p);
                        if (succBlk is BasicBlock)
                        {
                            newPath.AddLast(succBlk);
                            // add back
                            basicPaths.AddLast(newPath);
                        }
                        else if (succBlk is LoopHeadBlock)
                        {
                            newPath.AddLast(succBlk);
                            // check newPath
                            PrintBasicPath(newPath);

                            if (!accessed.Contains(succBlk))
                            {
                                // meeting loop for first time
                                basicPaths.AddLast(new BasicPath(new Block[] { succBlk }));
                            }
                        }
                        else if (succBlk is PostconditionBlock)
                        {
                            newPath.AddLast(succBlk);
                            // check newPath
                            PrintBasicPath(newPath);
                        }
                        accessed.Add(succBlk);
                    }
                }
            }
            return 1;
        }


        // debugging 

        private void PrintBasicPath(BasicPath p)
        {
            writer.WriteLine("Basic Path Start");
            foreach (Block b in p)
            {
                b.Print(writer);
            }
            writer.WriteLine("Basic Path End");
        }
    }
}