#!/usr/bin/env python
# -*- coding: utf-8 -*-
# vim: ts=4 sw=4 expandtab:

"""
此脚本自动测试当前目录下所有 *.decaf 程序，输出到 output 目录下，
并与 result 目录下的标准答案比较。

请注意我们在判分时会有更多的测试用例。
"""

import os
import subprocess
import sys, re

def read_txt_file(filename):
    with open(filename,'r') as f:
        txt = f.read().strip()
    # Python should be able to do it automatically, but just in case...
    txt = txt.replace('\r','').split('\n')
    result = []
    
    for line in txt:
        noc = line
        if "Error at" in line and ',' in line:
            FILTER = re.compile(r',[0-9]*\)')
            noc = FILTER.sub(r')',line)
            # noc = line[:line.index(',')] + line[line.index(')'):]
        result.append(noc)
    return '\n'.join(result)

def main():
    decaf_jar = os.path.join('..', '..', 'result', 'decaf.jar')
    names = sys.argv[-1]
    if '.py' in names:
        names = sorted(os.listdir('.'))
    else:
        names = [x for x in sorted(os.listdir('.')) if names in x]
    for name in names:
        bname,ext = os.path.splitext(name)
        if ext != '.decaf':
            continue
        # Run the test case, redirecting stdout/stderr to output/bname.result
        subprocess.call(['java', '-jar', decaf_jar, '-l', '1', name],
                stdout=open(os.path.join('output', bname + '.result'), 'w'),
                stderr=subprocess.STDOUT)
        # Check the result
        expected = read_txt_file(os.path.join('result',bname+'.out'))
        actual = read_txt_file(os.path.join('output',bname+'.result'))
        if expected == actual:
            info = 'OK :)'
        else:
            info = 'ERROR!'
            # os.system('diff result/%s.result output/%s.result' % (bname, bname))
        print('{0:<30}{1}'.format(name,info))
    if os.name == 'nt':
        print('Press Enter to continue...')
        try:
            raw_input() # Python 2
        except:
            input() # Python 3

if __name__ == '__main__':
    main()
