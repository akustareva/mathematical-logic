import checker
import transform
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
            if line[-1] == "\n":
                proof.append(line[:-1])
            else:
                proof.append(line)

    return header, proof

start = time.clock()
input_file = open('test.in', 'r')
output_file = open('answer.out', 'w')

header, proof = separation()

checker = checker.Checker()
check_result = checker.check_expression(header, proof)

if check_result[0]:
    print("correct")
else:
    print("incorrect")

if not check_result[0]:
    output_file.write("Вывод некорректен начиная с формулы номер " + str(check_result[1]))
else:
    if check_result[2] is None:
        output_file.write(header + "\n")
        for line in proof:
            output_file.write(line + "\n")
    else:       # deduction
        pos = header.find("|-")
        if len(check_result[3]) == 1:
            output_file.write("|-(" + check_result[3][0] + ")->(" + header[(pos + 2):] + ")\n")
        elif len(check_result[3]) > 1:
            second_part = "|-(" + check_result[3][-1] + ")->(" + header[(pos + 2):] + ")\n"
            check_result[3].pop()
            first_part = ""
            for hypothesis in check_result[3]:
                first_part += hypothesis + ","
            first_part = first_part[:-1]
            output_file.write(first_part + second_part)
        transform = transform.TransformationByDeduction()
        transformed = transform.get_proof(check_result[1], check_result[2])
        for line in transformed:
            output_file.write(str(line) + "\n")

end = time.clock()
print(end - start)
input_file.close()
output_file.close()