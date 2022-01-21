

import pandas as pd
from csp import CSP, backtracking_search, dom_wdeg, forward_checking, mrv, unordered_domain_values, first_unassigned_variable, mac, min_conflicts, lcv, examtimetable
import csv
import string
import time
import sys



def main():

    ####################################################################
    "arxika diavazoume to arxeio kai dimiourgoume mia lista apo Courses"
    with open("Στοιχεία Μαθημάτων.csv") as file:
        data_reader = csv.reader(file)
        rows = []
        variables = list()
        for line in (data_reader):
            rows.append(line)
        for row in rows[1:]:
            i=1
            for col in row:
                if i==1:
                    semester=int(col)
                    i = i+1
                elif i==2:
                    name = str(col)
                    i = i+1
                elif i==3:
                    teacher = str(col)
                    i = i+1
                elif i==4:
                    if col == 'FALSE':
                        difficulty = 'FALSE'
                    else:
                        difficulty = 'TRUE'
                    i = i+1
                elif i==5:
                    if col == 'FALSE':
                        lab = 'FALSE'
                    else:
                        lab = 'TRUE'
            var = str(semester) + ','+ str(name)+ ',' + str(teacher)+ ',' +str(difficulty)+ ',' + str(lab)
            variables.append(var)

            """theoro to ergatsirio os ksexoristo mathima, os dificulty tou vazo FALSE afou den leei 
            kati sigekrimeno i ekfonisi, an to mathima eixe difficulty tote 
            afou anagastika prepei na mpoun tin idia mera den epireazetai kapos o 
            periorismos gia ta diskola mathimata na apexoun toulaxistondio meres
            """
            if lab != 'FALSE':
                var = str(semester) + ','+ str(name)+ ',' + str(teacher)+ ',' +str('FALSE')+ ',' + str('yes')
                variables.append(var)

        
    ######################################################################
    #ektelountai oloi oi sindiasmoi ton algorithmon pou anaferei i ekfonisi me ena compilation tou programmatos
    totaldays=21
    csp = examtimetable(totaldays, variables)
    args = list(sys.argv)
    method = args[1]
    "klisi tou fc"
    if (int(method) == 1):
        print("\n")
        print("--------------------FC algorithm--------------------")
        print("\n")
        print("~~~~~~~~~~~~~~~~~~~~Using MRV~~~~~~~~~~~~~~~~~~~~")
        start = time.time()
        result= backtracking_search(csp, select_unassigned_variable=mrv, order_domain_values = lcv ,inference=forward_checking)
        end = time.time()
        if (result!=None):
            csp.display(assignment=result)
        print("Total assignments/visited nodes= %d" % (csp.nassigns))
        print("Algorithm took: %f" % (end - start), "seconds")
        print("Total constraint checks:", (csp.constraintsch))

    if(int(method)==2):
        print("\n")
        print("--------------------FC algorithm--------------------")
        print("\n")
        print("~~~~~~~~~~~~~~~~~~~~Using dom/wdeg~~~~~~~~~~~~~~~~~~~~")
        start = time.time()
        result= backtracking_search(csp, select_unassigned_variable=dom_wdeg, order_domain_values = lcv ,inference=forward_checking)
        end = time.time()
        if (result!=None):
            csp.display(assignment=result)
        print("Total assignments/visited nodes= %d" % (csp.nassigns))
        print("Algorithm took: %f" % (end - start), "seconds")
        print("Total constraint checks:", (csp.constraintsch))


    "klisi tou mac"
    if (int(method)==3):
        print("\n")
        print("--------------------MAC algorithm--------------------")
        print("\n")
        print("~~~~~~~~~~~~~~~~~~~~Using MRV~~~~~~~~~~~~~~~~~~~~")
        start = time.time()
        result = backtracking_search(csp, select_unassigned_variable=mrv, order_domain_values = lcv ,inference=mac)
        end = time.time()
        if (result!=None):
            csp.display(assignment=result)
        else:
            print("couldnt find solution")
        print("Total assignments/visited nodes= %d" % (csp.nassigns))
        print("Algorithm took: %f" % (end - start), "seconds")
        print("Total constraint checks:", (csp.constraintsch))
    
    if (int(method)==4):
        print("\n")
        print("--------------------MAC algorithm--------------------")
        print("\n")
        print("~~~~~~~~~~~~~~~~~~~~Using dom/wdeg~~~~~~~~~~~~~~~~~~~~")
        start = time.time()
        result = backtracking_search(csp, select_unassigned_variable=dom_wdeg, order_domain_values = lcv ,inference=mac)
        end = time.time()
        if (result!=None):
            csp.display(assignment=result)
        print("Total assignments/visited nodes= %d" % (csp.nassigns))
        print("Algorithm took: %f" % (end - start), "seconds")
        print("Total constraint checks:", (csp.constraintsch))
            



    "klisi tou min-conflicts"
    if (int(method)==5):
        print("\n")
        print("--------------------MIN_CONFLICTS algorithm--------------------")
        start = time.time()
        result = min_conflicts(csp)
        end = time.time()
        if (result!=None):
            csp.display(assignment=result)
        else:
            print("Min-conflicts couldn't find a solution")
        print("Total assignments/visited nodes= %d" % (csp.nassigns))
        print("Algorithm took: %f" % (end - start), "seconds")
        print("Total constraint checks:", (csp.constraintsch))


if __name__ == '__main__':
    main()



            


