import checker
import time


def separation():
    header = ""
    proof = []
    is_header = False

    for line in input_file:
        if not is_header:
            header = line[:-1]
            is_header = True
        else:
            if line[-1] == '\n':
                proof.append(line[:-1])
            else:
                proof.append(line)

    return header, proof

start = time.clock()
input_file = open('test.in', 'r')
output_file = open('answer.out', 'w')

header, proof = separation()

checker = checker.Checker()
tmp = checker.check_expression(header, proof)

if tmp[0]:
    print("correct")
else:
    print("first incorrect line: ", tmp[1])
end = time.clock()
print(end - start)
