/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System.IO;
using System.Collections.Generic;

namespace cminor
{
    using BasicBlockPath = LinkedList<Block>;
    class BasicPath
    {
        public Expression precondition = default!;
        public LinkedList<Statement> statements = new LinkedList<Statement>();
        public Expression postcondition = default!;

        public BasicPath() { }
        public BasicPath(BasicPath basicPath)
        {
            // do a deep copy for statements
            precondition = basicPath.precondition;
            postcondition = basicPath.postcondition;
            statements = new LinkedList<Statement>(basicPath.statements);
        }
    }

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

        // returns -1,0,1 similar to Apply
        private int checkedFunc(Function f)
        {
            if (f.blocks.Count == 0)
            {
                return 0;
            }
            HashSet<Block> accessed = new HashSet<Block>(); // check if a block has been accessed
            LinkedList<BasicBlockPath> basicPaths = new LinkedList<BasicBlockPath>(); // all basic paths used in bfs

            // init basicPaths
            basicPaths.AddLast(new BasicBlockPath(new Block[] { f.preconditionBlock }));
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

                    BasicBlockPath p = basicPaths.First.Value;
                    basicPaths.RemoveFirst();

                    if (p.Last is null)
                    {
                        // unknown error, each path should be nonempty
                        throw new System.Exception("Bug, each basic path should be nonnull");
                    }

                    foreach (Block succBlk in p.Last.Value.successors)
                    {
                        BasicBlockPath newPath = new BasicBlockPath(p);
                        if (succBlk is BasicBlock)
                        {
                            newPath.AddLast(succBlk);
                            basicPaths.AddLast(newPath);
                        }
                        else if (succBlk is LoopHeadBlock)
                        {
                            newPath.AddLast(succBlk);

                            if (!accessed.Contains(succBlk))
                            {
                                // meeting loop for first time, ccreate new path starting from lh
                                basicPaths.AddLast(new BasicBlockPath(new Block[] { succBlk }));
                            }
                        }
                        else if (succBlk is PostconditionBlock)
                        {
                            newPath.AddLast(succBlk);
                        }
                        else
                        {
                            // bug, unknown block type
                            throw new System.Exception("Bug, Unknown block type");
                        }

                        if (succBlk is LoopHeadBlock || succBlk is PostconditionBlock)
                        {
                            // forms a complete basic path, check
                            int retVal = checkBasicBlockPath(newPath);
                            switch (retVal)
                            {
                                case int n when (n == 0):
                                    return 0;
                                case int n when (n < 0):
                                    return -1;
                                default:
                                    break;
                            }
                        }

                        accessed.Add(succBlk);
                    }
                }
            }
            return 1;
        }

        private Expression getPrecondition(PreconditionBlock b)
        {
            Expression phi = new BoolConstantExpression(true);
            foreach (Expression e in b.conditions)
            {
                phi = new AndExpression(phi, e);
            }
            return phi;
        }
        private Expression getPrecondition(LoopHeadBlock b)
        {
            Expression phi = new BoolConstantExpression(true);
            foreach (Expression e in b.invariants)
            {
                phi = new AndExpression(phi, e);
            }
            return phi;
        }
        private Expression getPostCondition(PostconditionBlock b)
        {
            Expression psi = new BoolConstantExpression(false);
            foreach (Expression e in b.conditions)
            {
                psi = new OrExpression(psi, e);
            }
            return psi;
        }
        private Expression getPostCondition(LoopHeadBlock b)
        {
            Expression psi = new BoolConstantExpression(true);
            foreach (Expression e in b.invariants)
            {
                psi = new AndExpression(psi, e);
            }
            return psi;
        }


        private int checkBasicBlockPath(BasicBlockPath bbp)
        {
            PrintBasicBlockPath(bbp);

            BasicPath bp = new BasicPath();
            if (bbp.First.Value is PreconditionBlock)
            {
                bp.precondition = getPrecondition(bbp.First.Value as PreconditionBlock);
            }
            else if (bbp.First.Value is LoopHeadBlock)
            {
                bp.precondition = getPrecondition(bbp.First.Value as LoopHeadBlock);
            }
            else
            {
                throw new System.Exception("First that is not Precondition nor LoopHead");
            }

            LinkedListNode<Block> b = bbp.First;
            for (int i = 1; i < bbp.Count - 1; i++)
            {
                b = b.Next;
                foreach (Statement s in b.Value.statements)
                {
                    if (s is AssertStatement)
                    {
                        AssertStatement sAssert = s as AssertStatement;
                        BasicPath newBp = new BasicPath(bp);
                        newBp.postcondition = sAssert.pred;

                        checkBasicPath(newBp);

                        // assume statement from assert
                        AssumeStatement sAssume = new AssumeStatement();
                        sAssume.condition = sAssert.pred;

                        bp.statements.AddLast(sAssume);
                    }
                    else if (s is FunctionCallStatement)
                    {
                        FunctionCallStatement sFuncCall = s as FunctionCallStatement;
                        // generate new assert condition
                        Expression functionPrecondition = getPrecondition(sFuncCall.rhs.function.preconditionBlock);
                        List<LocalVariable> funcParams = sFuncCall.rhs.function.parameters;
                        List<LocalVariable> argParams = sFuncCall.rhs.argumentVariables;
                        for (int j = 0; j < argParams.Count; j++)
                        {
                            // substitute in argument params for function params
                            VariableExpression arg = new VariableExpression(argParams[j]);
                            functionPrecondition.Substitute(funcParams[j], arg);
                        }
                        BasicPath newBp = new BasicPath(bp);
                        newBp.postcondition = functionPrecondition;

                        checkBasicPath(newBp);

                        if (sFuncCall.lhs != null)
                        {
                            // substitute in lhs for rv
                            List<LocalVariable> funcRvs = sFuncCall.rhs.function.rvs;
                            Expression functionPostcondition = getPostCondition(sFuncCall.rhs.function.postconditionBlock);
                            for (int j = 0; j < sFuncCall.lhs.Count; j++)
                            {
                                VariableExpression lrv = new VariableExpression(sFuncCall.lhs[j]);
                                functionPostcondition.Substitute(funcRvs[j], lrv);
                            }
                            // set assume statement given by function return
                            AssumeStatement functionRetAssume = new AssumeStatement();
                            functionRetAssume.condition = functionPostcondition;
                            bp.statements.AddLast(functionRetAssume);
                        }
                    }
                    else
                    {
                        // other statements are not special
                        bp.statements.AddLast(s);
                    }
                }
            }


            if (bbp.Last.Value is PostconditionBlock)
            {
                bp.postcondition = getPostCondition(bbp.Last.Value as PostconditionBlock);
            }
            else if (bbp.Last.Value is LoopHeadBlock)
            {
                bp.postcondition = getPostCondition(bbp.Last.Value as LoopHeadBlock);
            }
            else
            {
                throw new System.Exception("Last that is not Lostcondition nor LoopHead");
            }

            checkBasicPath(bp);

            return 1;
        }

        private int checkBasicPath(BasicPath p)
        {
            PrintBasicPath(p);
            // PrintBasicPath(p);
            // Expression psi = new BoolConstantExpression(true);
            // LinkedListNode<Block> b = p.Last;
            // if (b.Value is PostconditionBlock)
            // {
            //     foreach (Expression e in (b.Value as PostconditionBlock).conditions)
            //     {
            //         psi = new AndExpression(psi, e);
            //     }
            // }
            // else
            // {

            // }

            // for (int i = 0; i < p.Count - 2; i++)
            // {
            //     b = b.Previous;
            //     foreach (Statement s in b.Value.statements)
            //     {
            //         if (s is AssumeStatement)
            //         {
            //             AssumeStatement sAssume = s as AssumeStatement;
            //             psi = new ImplicationExpression(sAssume.condition, psi);
            //         }
            //         else if (s is VariableAssignStatement)
            //         {
            //             VariableAssignStatement sAssign = s as VariableAssignStatement;
            //             psi = psi.Substitute(sAssign.variable, sAssign.rhs);
            //         }
            //     }
            // }

            // Expression phi = new BoolConstantExpression(false);
            // b = p.First;
            // foreach (Expression e in (b.Value as PreconditionBlock).conditions)
            // {
            //     phi = new OrExpression(phi, e);
            // }

            // ImplicationExpression check = new ImplicationExpression(phi, psi);
            // CounterModel c = solver.CheckValid(check);

            // if (c == null)
            // {
            //     return 1;
            // }
            return 1;
        }

        // debugging 
        private void PrintBasicBlockPath(BasicBlockPath p)
        {
            writer.WriteLine("Basic Block Path Start");

            foreach (Block b in p)
            {
                b.Print(writer);
            }

            writer.WriteLine("Basic Block Path End");
        }
        private void PrintBasicPath(BasicPath p)
        {
            writer.WriteLine("Basic Path Start");

            p.precondition.Print(writer);
            foreach (Statement s in p.statements)
            {
                s.Print(writer);
            }
            p.postcondition.Print(writer);

            writer.WriteLine("Basic Path Ends");
        }
    }
}