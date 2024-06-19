package Racos.ObjectiveFunction;

import MPC.*;
import Racos.Componet.Dimension;
import Racos.Componet.Instance;
import Racos.Time.TimeAnalyst;
import Racos.Tools.ValueArc;
import com.greenpineyu.fel.*;
import com.greenpineyu.fel.context.FelContext;

import java.util.*;

public class ObjectFunction implements Task {
    private Dimension dim;
    private Combination combination;
    private Automata product;
    private int automata_num;
    public TimeAnalyst timeAnalyst;
    //    private int []path1;
//    private int []path2;
    private FelEngine fel;
    private FelContext ctx;
    private ArrayList<ArrayList<HashMap<String, Double>>> allParametersValuesList;
    public double delta;
    private double penalty = 0;
    private double globalPenalty = 0;
    private boolean sat = true;
    private double cerr = 0.01;
    public ArrayList<ArrayList<Boolean>> infeasiblelist;
    public ArrayList<ArrayList<Integer>> path;
    int rangeParaSize;
    int armParaSize;
    int cmdSize;
    int actualCmdSize;
    int maxpathSize;
    double zeroTime, prepareTime;
    Random random = new Random();
    ArrayList<ArrayList<Double>> args = new ArrayList<>();
    InverseSolution IS;
    int locsize;
    ArrayList<ArrayList<Integer>> PathMap;
//    ArrayList<Boolean> infeasible_loc1;
//    ArrayList<Boolean> infeasible_loc2;

    public ValueArc valueArc;

    double[] time = new double[4];
    private double XtarMAX;
    private double RtarMAX;
    private double VMAX;

    public ObjectFunction(Combination combination, int maxPathSize, TimeAnalyst timeAnalyst) {
        this.combination = combination;
        product = combination.product;
        automata_num = 1;
        dim = new Dimension();
        delta = combination.delta;
        maxpathSize = maxPathSize;
        this.PathMap = combination.PathMap;
        this.timeAnalyst = timeAnalyst;
        IS = new InverseSolution();
        VMAX = 150;
        XtarMAX = 210;
        RtarMAX = 180;
//        this.combinPath=combination.combin;

        rangeParaSize = (product.rangeParameters == null) ? 0 : product.rangeParameters.size();
        armParaSize = 9;
        cmdSize = (maxPathSize - 4) / 3 - 1;
        dim.setSize(1 + armParaSize * cmdSize + rangeParaSize + (combination.ca.staytime4loc ? maxpathSize : 0));

        int index = 0;
        dim.setDimension(index++, 0, PathMap.size() - 1, false);

        while (index < 1 + armParaSize * cmdSize) {
            int up = 3;
            for (int i = 0; i < up; i++) {
                if (i == up - 1) {
                    dim.setDimension(index++, 0, XtarMAX, true);

                } else dim.setDimension(index++, (-1) * XtarMAX, XtarMAX, true);
            }
            for (int i = 0; i < up; i++) {
                dim.setDimension(index++, -RtarMAX, RtarMAX, true);
            }
            dim.setDimension(index++, 16, VMAX, true);
            dim.setDimension(index++, 10, 40, true);
            dim.setDimension(index++, 10, 40, true);

        }
        for (int i = 0; i < rangeParaSize; ++i)
            dim.setDimension(index++, product.rangeParameters.get(i).lowerBound, product.rangeParameters.get(i).upperBound, true);


        if (combination.ca.staytime4loc) {
            for (int i = 0; i < maxPathSize; ++i) {
                if (combination.ca.addInit && i == 0) {
                    dim.setDimension(i + rangeParaSize + 1, 1, 1, false);
                    continue;
                }
                dim.setDimension(i + rangeParaSize + 1, 1, 300, false);
            }
        }
        fel = new FelEngineImpl();
        ctx = fel.getContext();
        valueArc = new ValueArc();
    }


    public int getPathLength() {
        return this.maxpathSize;
    }

    public boolean checkConstraints(String forbidden, HashMap<String, Double> parametersValues) {
        for (Map.Entry<String, Double> entry : parametersValues.entrySet()) {
            ctx.set(entry.getKey(), entry.getValue());
        }
        if (forbidden == null)
            return true;
        boolean result = (boolean) fel.eval(forbidden);
        if (!result) return true;
        sat = false;
        globalPenalty += computeConstraintValue(forbidden.trim());
        return false;
    }

    public boolean checkConstraints(Automata automata, HashMap<String, Double> parametersValues) {
        for (Map.Entry<String, Double> entry : parametersValues.entrySet()) {
            ctx.set(entry.getKey(), entry.getValue());
        }
        if (automata.forbiddenConstraints == null)
            return true;
        boolean result = (boolean) fel.eval(automata.forbiddenConstraints);
        if (!result) return true;
        sat = false;
        globalPenalty += computeConstraintValue(automata.forbiddenConstraints.trim());
        return false;
    }

    public double computeConstraintValue(String constraint) {
        int firstRightBracket = constraint.trim().indexOf(")");
        if (firstRightBracket != -1 && constraint.indexOf('&') == -1 && constraint.indexOf('|') == -1)
            return computePenalty(constraint.substring(constraint.indexOf('(') + 1, constraint.lastIndexOf(")")), false);
        if (firstRightBracket != -1 && firstRightBracket != constraint.length() - 1) {
            for (int i = firstRightBracket; i < constraint.length(); ++i) {
                if (constraint.charAt(i) == '&') {
                    int index = 0;
                    int numOfBrackets = 0;
                    int partBegin = 0;
                    double pen = 0;
                    while (index < constraint.length()) {
                        if (constraint.charAt(index) == '(')
                            ++numOfBrackets;
                        else if (constraint.charAt(index) == ')')
                            --numOfBrackets;
                        else if (constraint.charAt(index) == '&' && numOfBrackets == 0) {
                            String temp = constraint.substring(partBegin, index);
                            boolean result = (boolean) fel.eval(temp);
                            if (!result) return 0;
                            else pen += computeConstraintValue(temp);
                            index = index + 2;
                            partBegin = index;
                            constraint = constraint.substring(index);
                            continue;
                        }
                        ++index;
                    }
                    return pen;
                } else if (constraint.charAt(i) == '|') {
                    int index = 0;
                    int numOfBrackets = 0;
                    int partBegin = 0;
                    double minPen = Double.MAX_VALUE;
                    while (index < constraint.length()) {
                        if (constraint.charAt(index) == '(')
                            ++numOfBrackets;
                        else if (constraint.charAt(index) == ')')
                            --numOfBrackets;
                        else if (constraint.charAt(index) == '|' && numOfBrackets == 0) {
                            String temp = constraint.substring(partBegin, index);
                            boolean result = (boolean) fel.eval(temp);
                            if (result) {
                                temp = temp.trim();
                                minPen = (computeConstraintValue(temp) < minPen) ? computeConstraintValue(temp) : minPen;
                            }
                            index = index + 3;
                            partBegin = index;

                            continue;
                        }
                        ++index;
                    }
                    return minPen;
                }
            }
        } else {
            if (firstRightBracket != -1) {
                constraint = constraint.substring(constraint.indexOf('(') + 1, firstRightBracket);
            }
            if (constraint.indexOf('&') != -1) {
                String[] strings = constraint.split("&");
                double pen = 0;
                for (int i = 0; i < strings.length; ++i) {
                    if (strings[i].equals("")) continue;
                    boolean result = (boolean) fel.eval(strings[i]);
                    if (!result) return 0;
                    else pen += computeConstraintValue(strings[i]);
                }
                return pen;
            } else if (constraint.indexOf('|') != -1) {
                String[] strings = constraint.split("\\|");
                double minPen = Double.MAX_VALUE;
                for (int i = 0; i < strings.length; ++i) {
                    if (strings[i].equals("")) continue;
                    boolean result = (boolean) fel.eval(strings[i]);
                    if (!result) continue;
                    else
                        minPen = (computeConstraintValue(strings[i]) < minPen) ? computeConstraintValue(strings[i]) : minPen;
                }
                return minPen;
            } else return computePenalty(constraint, false);
        }
        return 0;
    }

    public HashMap<String, Double> computeValuesByFlow(HashMap<String, Double> parametersValues, Location location, double arg) {
        HashMap<String, Double> tempMap = new HashMap<>();
        for (HashMap.Entry<String, Double> entry : parametersValues.entrySet()) {
            ctx.set(entry.getKey(), entry.getValue());
        }
        for (HashMap.Entry<String, Double> entry : parametersValues.entrySet()) {
            if (location.flows.containsKey(entry.getKey())) {
                String expression = location.flows.get(entry.getKey());
                expression = expression.replaceAll("phi\\(([^)]+)\\)", "($1 <= 2 ? 1 : $1 <= 5 ? 2 : 3)");

//                if (expression.contains("phi(drone_vx)")) {
//                    if (parametersValues.get("drone_vx") <= 2)
//                        expression = expression.replace("phi(drone_vx)", "1");
//                    else if (parametersValues.get("drone_vx") <= 5)
//                        expression = expression.replace("phi(drone_vx)", "2");
//                    else
//                        expression = expression.replace("phi(drone_vx)", "3");
//                }
//                if (expression.contains("phi(drone_vy)")) {
//                    if (parametersValues.get("drone_vy") <= 2)
//                        expression = expression.replace("phi(drone_vy)", "1");
//                    else if (parametersValues.get("drone_vy") <= 5)
//                        expression = expression.replace("phi(drone_vy)", "2");
//                    else
//                        expression = expression.replace("phi(drone_vy)", "3");
//                }
                double currentTime = System.currentTimeMillis();
                Object obj = fel.eval(expression);
                double endTime = System.currentTimeMillis();
                double temptime = (endTime - currentTime) / 1000;
                time[3] += temptime;
                double result;
                if (obj instanceof Double)
                    result = (double) obj;
                else if (obj instanceof Integer) {
                    result = (int) obj;
                } else if (obj instanceof Long) {
                    result = ((Long) obj).doubleValue();
                } else {
                    result = 0;
                    System.out.println("Not Double and Not Integer!");
                    System.out.println(obj.getClass().getName());
                    System.out.println(obj);
                    System.out.println(location.flows.get(entry.getKey()));
                    System.exit(0);
                }
                double delta = result * arg;
                tempMap.put(entry.getKey(), entry.getValue() + delta);
            } else {
                tempMap.put(entry.getKey(), entry.getValue());
            }
        }
        return tempMap;

    }

    public boolean checkGuards(Automata automata, int index) {
        ArrayList<Integer> path_tmp = path.get(index);

        int[] path = new int[path_tmp.size()];
        for (int i = 0; i < path_tmp.size(); i++) {
            path[i] = path_tmp.get(i);
        }

        ArrayList<HashMap<String, Double>> allParametersValues = allParametersValuesList.get(index);

        for (int i = 0; i < path.length; ++i) {
            Location location = automata.locations.get(path[i]);
            if (i >= allParametersValues.size()) {
                int sad = 1;
                sad++;
            }
            HashMap<String, Double> parameterValues = allParametersValues.get(i);
            int target;
            if (i + 1 < path.length) {
                target = path[i + 1];
                int source = path[i];
                for (int k = 0; k < automata.transitions.size(); ++k) {
                    Transition transition = automata.transitions.get(k);
                    if (transition.source == source && transition.target == target) {
                        for (Map.Entry<String, Double> entry : parameterValues.entrySet()) {
                            ctx.set(entry.getKey(), entry.getValue());
                        }
                        for (int guardIndex = 0; guardIndex < transition.guards.size(); ++guardIndex) {
                            boolean result = (boolean) fel.eval(transition.guards.get(guardIndex));
                            if (!result) {
                                String guard = transition.guards.get(guardIndex);
                                if (Double.isNaN(computePenalty(guard, false))) {
                                    sat = false;
                                    penalty += 100000;
                                } else if (computePenalty(guard, false) > cerr) {
                                    sat = false;
                                    penalty += computePenalty(guard, false);
                                }
                            }
                        }
                    }
                }
            }
        }

        return true;
    }

    public double checkCombine(ArrayList<HashMap<String, Double>> newMap) {
        double res = 0;
//        for(int i=0;i< newMap.size();i++){
//            for(int j=i+1;j< newMap.size();j++){
//                HashMap<String,Double> newMap1=newMap.get(i);
//                HashMap<String,Double> newMap2=newMap.get(j);
//                res=Math.pow(newMap1.get("x")-newMap2.get("x"),2)+Math.pow(newMap1.get("y")-newMap2.get("y"),2);
//                if(res<0.01) {
//                    sat=false;
//                    globalPenalty+=res;
//                }
//            }
//        }
        return res;
    }

    public void updateFastInfo(ArrayList<HashMap<String, Double>> allmap, ArrayList<Integer> locIndexList) {
        for (int i = 0; i < automata_num; i++) {
            int locIndex = locIndexList.get(i);
            if (locIndex < path.get(i).size()) {
                String locName = product.locations.get(path.get(i).get(locIndex)).name;
                HashMap<String, Double> newMap1 = allmap.get(i);
                if (locName.contains("fp")) {
                    double A1_THETA1 = Math.toRadians(newMap1.get("arm_theta1"));
                    double A1_THETA2 = Math.toRadians(newMap1.get("arm_theta2"));
                    double A1_THETA3 = Math.toRadians(newMap1.get("arm_theta3"));
                    double A1_THETA4 = Math.toRadians(newMap1.get("arm_theta4"));
                    double A1_THETA5 = Math.toRadians(newMap1.get("arm_theta5"));
                    double A1_THETA6 = Math.toRadians(newMap1.get("arm_theta6"));

                    double x = Math.sin(A1_THETA1) * (-25.28 * Math.cos(A1_THETA5) * Math.sin(A1_THETA4) - 10 * Math.cos(A1_THETA6) * Math.sin(A1_THETA4) * Math.sin(A1_THETA5) - 10 * Math.cos(A1_THETA4) * Math.sin(A1_THETA6)) + Math.cos(A1_THETA1) * (29.69 + Math.sin(A1_THETA2) * (108. + Math.sin(A1_THETA3) * (-168.98 - 10 * Math.cos(A1_THETA5) * Math.cos(A1_THETA6) + 25.28 * Math.sin(A1_THETA5)) + Math.cos(A1_THETA3) * (20. + Math.cos(A1_THETA4) * (-25.28 * Math.cos(A1_THETA5) - 10 * Math.cos(A1_THETA6) * Math.sin(A1_THETA5)) + 10 * Math.sin(A1_THETA4) * Math.sin(A1_THETA6))) + Math.cos(A1_THETA2) * (Math.cos(A1_THETA3) * (168.98 + 10 * Math.cos(A1_THETA5) * Math.cos(A1_THETA6) - 25.28 * Math.sin(A1_THETA5)) + Math.sin(A1_THETA3) * (20. + Math.cos(A1_THETA4) * (-25.28 * Math.cos(A1_THETA5) - 10 * Math.cos(A1_THETA6) * Math.sin(A1_THETA5)) + 10 * Math.sin(A1_THETA4) * Math.sin(A1_THETA6))));
                    double y = Math.cos(A1_THETA1) * (25.28 * Math.cos(A1_THETA5) * Math.sin(A1_THETA4) + 10. * Math.cos(A1_THETA6) * Math.sin(A1_THETA4) * Math.sin(A1_THETA5) + 10. * Math.cos(A1_THETA4) * Math.sin(A1_THETA6)) + Math.sin(A1_THETA1) * (29.69 + Math.sin(A1_THETA2) * (108. + Math.sin(A1_THETA3) * (-168.98 - 10. * Math.cos(A1_THETA5) * Math.cos(A1_THETA6) + 25.28 * Math.sin(A1_THETA5)) + Math.cos(A1_THETA3) * (20. + Math.cos(A1_THETA4) * (-25.28 * Math.cos(A1_THETA5) - 10. * Math.cos(A1_THETA6) * Math.sin(A1_THETA5)) + 10. * Math.sin(A1_THETA4) * Math.sin(A1_THETA6))) + Math.cos(A1_THETA2) * (Math.cos(A1_THETA3) * (168.98 + 10. * Math.cos(A1_THETA5) * Math.cos(A1_THETA6) - 25.28 * Math.sin(A1_THETA5)) + Math.sin(A1_THETA3) * (20. + Math.cos(A1_THETA4) * (-25.28 * Math.cos(A1_THETA5) - 10. * Math.cos(A1_THETA6) * Math.sin(A1_THETA5)) + 10. * Math.sin(A1_THETA4) * Math.sin(A1_THETA6))));
                    double z = 127. - 20. * Math.sin(A1_THETA2) * Math.sin(A1_THETA3) + 25.28 * Math.cos(A1_THETA4) * Math.cos(A1_THETA5) * Math.sin(A1_THETA2) * Math.sin(A1_THETA3) + 10. * Math.cos(A1_THETA4) * Math.cos(A1_THETA6) * Math.sin(A1_THETA2) * Math.sin(A1_THETA3) * Math.sin(A1_THETA5) + Math.cos(A1_THETA3) * Math.sin(A1_THETA2) * (-168.98 - 10. * Math.cos(A1_THETA5) * Math.cos(A1_THETA6) + 25.28 * Math.sin(A1_THETA5)) - 10. * Math.sin(A1_THETA2) * Math.sin(A1_THETA3) * Math.sin(A1_THETA4) * Math.sin(A1_THETA6) + Math.cos(A1_THETA2) * (108. + Math.sin(A1_THETA3) * (-168.98 - 10. * Math.cos(A1_THETA5) * Math.cos(A1_THETA6) + 25.28 * Math.sin(A1_THETA5)) + Math.cos(A1_THETA3) * (20. + Math.cos(A1_THETA4) * (-25.28 * Math.cos(A1_THETA5) - 10. * Math.cos(A1_THETA6) * Math.sin(A1_THETA5)) + 10. * Math.sin(A1_THETA4) * Math.sin(A1_THETA6)));

                    newMap1.put("arm_x1", x);
                    newMap1.put("arm_x2", y);
                    newMap1.put("arm_x3", z);
                }
            }

        }
    }

    public HashMap<String, Double> computeValuesByFlowForArmBelt(HashMap<String, Double> parametersValues, int index, int locIndex, double arg) {

        HashMap<String, Double> tempMap = (HashMap<String, Double>) parametersValues.clone();
//        System.out.println("we need to ode in loc:" +locIndex);
        Location location = product.locations.get(locIndex);
        for (HashMap.Entry<String, Double> entry : parametersValues.entrySet()) {
            ctx.set(entry.getKey(), entry.getValue());
        }
        for (HashMap.Entry<String, String> entry : location.flows.entrySet()) {
            String expression;
            if (entry.getKey().contains("omega") || entry.getKey().contains("v")) {
                if (isdigit(entry.getValue().trim())) {
                    expression = entry.getValue();
                } else expression = entry.getValue();

                Object obj = fel.eval(expression);
                double result;
                if (obj instanceof Double)
                    result = (double) obj;
                else if (obj instanceof Integer) {
                    result = (int) obj;
                } else if (obj instanceof Long) {
                    result = ((Long) obj).doubleValue();
                } else {
                    result = 0;
                    System.out.println("Not Double and Not Integer!");
                    System.out.println(obj.getClass().getName());
                    System.out.println(obj);
                    System.out.println(location.flows.get(entry.getKey()));
                    System.exit(0);
                }
                double delta = result * arg;
                String var_name = entry.getKey();
//                System.out.println("varname:"+var_name);
                double res = parametersValues.get(var_name) + delta;
                tempMap.put(var_name, res);
                ctx.set(var_name, res);
            }

        }

        for (HashMap.Entry<String, String> entry : location.flows.entrySet()) {
            String expression;
            if (entry.getKey().contains("omega") || entry.getKey().contains("v")) {
            } else {
                if (isdigit(entry.getValue().trim())) {
                    expression = entry.getValue();
                } else expression = entry.getValue();
                //double result=tempMap.get(expression);

                try {
                    Object obj = fel.eval(expression);
                } catch (Exception e) {
                    System.out.println(expression);
                    System.out.println("error");
                }

                Object obj = fel.eval(expression);
                double result;
                if (obj instanceof Double)
                    result = (double) obj;
                else if (obj instanceof Integer) {
                    result = (int) obj;
                } else if (obj instanceof Long) {
                    result = ((Long) obj).doubleValue();
                } else {
                    result = 0;
                    System.out.println("Not Double and Not Integer!");
                    System.out.println(obj.getClass().getName());
                    System.out.println(obj);
                    System.out.println(location.flows.get(entry.getKey()));
                    System.exit(0);
                }
                double delta = result * arg;
                String var_name = entry.getKey();
                double res = parametersValues.get(var_name) + delta;
                tempMap.put(var_name, res);
                ctx.set(var_name, res);

            }
        }
        return tempMap;
    }


    public boolean isdigit(String s) {
        for (int i = 0; i < s.length(); i++) {
            if ((s.charAt(i) > '9' || s.charAt(i) < '0') && s.charAt(i) != '.' && s.charAt(i) != '-' && s.charAt(i) != 'E')
                return false;
        }
        return true;
    }

    public boolean checkInvarientsByODEForArmBelt(ArrayList<ArrayList<Double>> argsList, Instance ins) {
        ArrayList<Double> arg = args.get(0);//这里只有一组时间
        double curTime = 0;
        int cmdIndex = 0;
        HashMap<String, Double> newMap = product.duplicateInitParametersValues();
        ArrayList<HashMap<String, Double>> allstepMap = new ArrayList<>();
        allstepMap.add(newMap);

        ArrayList<Integer> locIndexList = new ArrayList<>();
        ArrayList<Boolean> nextLoc = new ArrayList<>();
        locIndexList.add(0);
        nextLoc.add(false);

        while (true) {
            double delta1 = delta;
            int curLocIndex = locIndexList.get(0);
            if (curLocIndex == arg.size()) {
                if(arg.size()<path.get(0).size())
                    arg.add(delta+curTime);
                else break;
            }
            double curLocTime = arg.get(curLocIndex);
            delta1 = Math.min(delta1, curLocTime - curTime);

            if (curTime == curLocTime) nextLoc.set(0, true);

            if (delta1 != 0) {
                int locIndex = locIndexList.get(0);
                newMap = allstepMap.get(0);

                newMap = computeValuesByFlowForArmBelt(newMap, 0, path.get(0).get(locIndex), delta1);
                allstepMap.set(0, newMap);
                updateFastInfo(allstepMap, locIndexList);//fast mode need to calculate X

            }

            int n = 0;
            if (nextLoc.get(0)) {
                int locIndex = locIndexList.get(0);
                if(locIndex==path.get(0).size()-1) break;
                locIndexList.set(n, locIndex + 1);
                nextLoc.set(n, false);
                if (locIndex < path.get(n).size() - 2) {
                    Transition transition = product.getTransitionBySourceAndTarget(path.get(n).get(locIndex), path.get(n).get(locIndex + 1));
                    if (transition == null) {
                        System.out.println("Found no transition");
                        System.exit(-1);
                    }

                    Location loc = product.locations.get(path.get(n).get(locIndex + 1));
                    if (loc.name.equals("zero,prepare")) {
                        ArrayList<Integer> locList = findZero(path.get(n), locIndex + 1);
                        setZero(curLocTime, ins, path.get(n).get(locIndex + 1), newMap, locList);
                        prepareTime = product.initParameterValues.get("belt_upperT");
                        int zero = 0, prepare = 0;
                        for (int p = locIndex + 1; p < path.get(n).size(); p++) {
                            String locName = product.locations.get(path.get(n).get(p)).name;
                            if (locName.contains("zero")) zero++;
                            if (locName.contains("prepare")) prepare++;
                        }


                        double last_time=curTime;
                        if (zero > prepare) {
                            if (zeroTime < prepareTime) {
                                sat = false;
                                penalty += zeroTime - prepareTime;
                                return false;
                            }

                            arg.add(last_time+prepareTime);
                            last_time+=prepareTime;
                            zero--;
                            double restTime = (zeroTime - prepareTime) / zero;
                            for (int i = 0; i < zero; i++) {
                                arg.add(last_time+restTime);
                                last_time+=restTime;
                            }
                        } else if (zero == prepare) {
                            if (zeroTime > prepareTime) {
                                sat = false;
                                penalty += zeroTime - prepareTime;
                                return false;
                            }
                            arg.add(last_time+prepareTime);

                        } else {
                            if (zeroTime > prepareTime) {
                                sat = false;
                                penalty += zeroTime - prepareTime;
                                return false;
                            }
                            arg.add(last_time+zeroTime);
                            last_time+=zeroTime;
                            prepare--;
                            double restTime = (prepareTime - zeroTime) / prepare;
                            for (int i = 0; i < prepare; i++) {
                                arg.add(last_time+restTime);
                                last_time+=restTime;
                            }
                        }


                    }


                    if (transition.label.contains("change")) {
                        ArrayList<Integer> locList = new ArrayList<>();
                        locList.add(path.get(n).get(locIndex + 1));
                        locList.add(path.get(n).get(locIndex + 2));
                        locList.add(path.get(n).get(locIndex + 3));
                        locList.add(path.get(n).get(locIndex ));
                        setNextThreeLoc(curLocTime, ++cmdIndex, ins, n, path.get(n).get(locIndex + 1), newMap, locList);
                    }
                    for (HashMap.Entry<String, String> entry : transition.assignments.entrySet()) {
                        Object obj = fel.eval(entry.getValue());
                        double result = 0;
                        if (obj instanceof Integer) result = (int) obj;
                        else if (obj instanceof Double) result = (double) obj;
                        else {
                            System.out.println("Not Double and Not Integer!");
                            System.out.println(entry.getValue());
                            System.exit(0);
                        }

                        allstepMap.get(n).put(entry.getKey(), result);
                    }
                }

            }
            curTime += delta1;

        }
        return true;
    }

    private ArrayList<Integer> findZero(ArrayList<Integer> path, int cur) {
        ArrayList<Integer> ans = new ArrayList<>();
        for (int i = cur; i < path.size(); i++) {
            if (product.locations.get(path.get(i)).name.contains("zero"))
                ans.add(path.get(i));
        }
        return ans;
    }


    private void setZero(double surStep, Instance ins, Integer locId, HashMap<String, Double> newMap, ArrayList<Integer> locList) {
        double[] X_tar = new double[3];
        double[] R_tar = new double[3];
        double[] current_Theta = new double[6];//current theta
        double[] current_X = new double[3];
        double[] current_R = new double[3];
        double[] delta_X = new double[3];
        double lastTime = surStep;
        Automata automata = product;


        for (int index = 0; index < 6; index++) {
            current_Theta[index] = newMap.get("arm_theta" + Integer.toString(index + 1));
        }
        //current_X=getFastInfo();
        for (int index = 0; index < 3; index++) {
            current_X[index] = newMap.get("arm_x" + Integer.toString(index + 1));
            current_R[index] = newMap.get("arm_r" + Integer.toString(index + 1));
        }

        String name = automata.locations.get(locId).name;

        X_tar[0] = product.initParameterValues.get("arm_x1");
        X_tar[1] = product.initParameterValues.get("arm_x2");
        X_tar[2] = product.initParameterValues.get("arm_x3");

        R_tar[0] = product.initParameterValues.get("arm_r1");
        R_tar[1] = product.initParameterValues.get("arm_r2");
        R_tar[2] = product.initParameterValues.get("arm_r3");


        double[] theta_tar = IS.F_inverse(X_tar, R_tar, current_Theta);
        double[] delta_theta = new double[6];
        for (int j = 0; j < 6; j++) {

            delta_theta[j] = theta_tar[j] - current_Theta[j];
        }
        double[] t = IS.Solve_T12_zero(delta_theta);
        double[] theta_speed_fast = IS.theta_speed;
        setZeroFlow(t, lastTime, locId, delta_theta, theta_speed_fast,locList);

    }

    void setZeroFlow(double[] T12, double lastTime, int locIndex, double[] delta_theta, double[] theta_speed_fast,ArrayList<Integer> loclist) {
        //T12[0]=tamx,T12[0]=t2
        double t2 = T12[0] + lastTime;

        String tmp2 = "";
        for (int i = 0; i < 6; i++) {
            tmp2 = tmp2 + "theta" + Integer.toString(i + 1) + "'=" + Double.toString(theta_speed_fast[i]) + "&amp;";
        }
        for(int i=0;i<loclist.size();i++){
            Location location = product.locations.get(loclist.get(i));
            location.setFlow(tmp2, product.parameters);
        }

        zeroTime = T12[0];

    }

    private void setNextThreeLoc(double surStep, int cmdId, Instance ins, int autId, int locId, HashMap<String, Double> newMap, ArrayList<Integer> locList) {
        double[] X_tar = new double[3];
        double[] R_tar = new double[3];
        double[] current_Theta = new double[6];//current theta
        double[] current_X = new double[3];
        double[] current_R = new double[3];
        double[] delta_X = new double[3];
        double[] delta_R = new double[3];
        double[] theta = new double[6];
        double[] X = new double[3];
        double[] R = new double[3];
        double lastTime = surStep;
        double Height;
        double V_tar;

        Automata automata = product;

        for (int index = 0; index < 6; index++) {
            current_Theta[index] = newMap.get("arm_theta" + Integer.toString(index + 1));
        }
        //current_X=getFastInfo();
        for (int index = 0; index < 3; index++) {
            current_X[index] = newMap.get("arm_x" + Integer.toString(index + 1));
            current_R[index] = newMap.get("arm_r" + Integer.toString(index + 1));
        }

        String name = automata.locations.get(locId).name;

        int current_index = 1 + armParaSize * (cmdId - 1);
        if (cmdId < actualCmdSize) {
            X_tar[0] = ins.getFeature(current_index) + current_X[0];
            X_tar[1] = ins.getFeature(current_index + 1) + current_X[1];
            X_tar[2] = ins.getFeature(current_index + 2) + current_X[2];
            current_index += 3;
            R_tar[0] = ins.getFeature(current_index);
            R_tar[1] = ins.getFeature(current_index + 1);
            R_tar[2] = ins.getFeature(current_index + 2);
            current_index += 3;

            V_tar = ins.getFeature(current_index);
            current_index += 1;

            Height = ins.getFeature(current_index);
            current_index += 1;
        } else {
            X_tar[0] = 60;
            X_tar[1] = 240;
            X_tar[2] = 180;

            R_tar[0] = 0;
            R_tar[1] = -25;
            R_tar[2] = -90;

            V_tar = 20;

            Height = 10;
        }

        double[] theta_tar = IS.F_inverse(X_tar, R_tar, current_Theta);
        while (theta_tar[0] == 1000 || X_tar[2] < 0) {
            current_index -= 8;
            for (int k = 0; k < 8; k++) {
                ins.setFeature(current_index + k, dim.getRegion(current_index + k)[0] + random.nextDouble() * (dim.getRegion(current_index + k)[1] - dim.getRegion(current_index + k)[0]));
            }

            X_tar[0] = ins.getFeature(current_index) + current_X[0];
            X_tar[1] = ins.getFeature(current_index + 1) + current_X[1];
            X_tar[2] = ins.getFeature(current_index + 2) + current_X[2];
            current_index += 3;

            R_tar[0] = 0;
            R_tar[1] = -25;
            R_tar[2] = -90;
            current_index += 3;

            V_tar = ins.getFeature(current_index);
            current_index += 1;

            Height = ins.getFeature(current_index);
            current_index += 1;


            //Calculate inverse solution for theta
            theta_tar = IS.F_inverse(X_tar, R_tar, current_Theta);
        }


        if (name.contains("fp")) {
            //fast
            double[] delta_theta = new double[6];
            for (int j = 0; j < 6; j++) {
                delta_theta[j] = theta_tar[j] - current_Theta[j];
            }
            double[] t = IS.Solve_T12(delta_theta);
            double[] a_fast = IS.a_fast;
            double[] w_fast = IS.w_fast;
            setFast(t, lastTime, locId, locList, a_fast, w_fast);

            theta = theta_tar.clone();
            X = X_tar.clone();
            R = R_tar.clone();
            lastTime += t[2];
            current_index += 3;
        } else if (name.contains("lp")) {
            //forward
            for (int j = 0; j < 3; j++) {
                delta_X[j] = X_tar[j] - current_X[j];
            }

            double[] t = IS.Solve_T12_forward(delta_X, V_tar);
            double[] a_forward = IS.a_forward;
            double[] v_forward = IS.v_forward;

            setForward(t, lastTime, locId, theta_tar, a_forward, v_forward,locList);

        } else {
            //doorlike
            double[] tmp_tar1 = new double[]{current_X[0], current_X[1], current_X[2] + Height};
            double[] tmp_tar2 = new double[]{X_tar[0], X_tar[1], X_tar[2] + Height};


            for (int j = 0; j < 3; j++) {
                delta_X[j] = tmp_tar2[j] - tmp_tar1[j];
            }
            double[] t = IS.Solve_T12_doorlike(delta_X, Height);
            double[] v_doorlike = IS.v_doorlike;
            setDoorlike(t, lastTime, locId, theta_tar, v_doorlike, IS.v_max,locList);
        }


    }

    private void setDoorlike(double[] time, double lastTime, int locIndex, double[] theta_tar, double[] v_doorlike, double v_max,ArrayList<Integer> locList) {
        double t1 = time[0] + lastTime;
        double t2 = time[1] + lastTime;
        double t3 = time[2] + lastTime;
        String tmp = "";
        for (int i = 0; i < 6; i++) {
            tmp = tmp + "arm_theta" + Integer.toString(i + 1) + "=" + Double.toString(theta_tar[i]) + " &&";

        }
        Transition transition1 = product.getTransitionBySourceAndTarget(locList.get(3), locList.get(0));
        //todo forward mode is not the first mode
        transition1.setAssignment(tmp, product.parameters);


        String tmp1 = "arm_x3'=" + Double.toString(v_max) + "&&";
        String tmp2 = "";
        String tmp3 = "arm_x3'=" + Double.toString(v_max * (-1)) + "&&";

        for (int i = 0; i < 3; i++) {
            tmp2 = tmp2 + "arm_x" + Integer.toString(i + 1) + "'=" + Double.toString(v_doorlike[i]) + "&&";
        }
        Location location = product.locations.get(locList.get(0));
        location.setFlow(tmp1, product.parameters);
        Transition transition = product.getTransitionBySourceAndTarget(locIndex + 1, locIndex + 2);

        location = product.locations.get(locList.get(1));
        location.setFlow(tmp2, product.parameters);
        transition = product.getTransitionBySourceAndTarget(locIndex + 2, locIndex + 3);

        location = product.locations.get(locList.get(2));
        location.setFlow(tmp3, product.parameters);
    }

    void setFast(double[] T12, double lastTime, int locIndex, ArrayList<Integer> locList, double[] a_fast, double[] w_fast) {
        //T12[0]=tamx,T12[0]=t2
        double t1 = T12[0] + lastTime;
        double t2 = T12[1] + lastTime;
        double t3 = T12[2] + lastTime;
        if (locIndex != 0) {
//            Transition transition=product.getTransitionBySourceAndTarget(path.get(Auto_index).get(locIndex),path.get(Auto_index).get(locIndex+1));

            Transition transition = product.getTransitionBySourceAndTarget(locIndex - 1, locIndex);
            //todo fast mode is not the first mode
        }
        String tmp1 = "";
        String tmp2 = "";
        String tmp3 = "";
        for (int i = 0; i < 6; i++) {
            tmp1 = tmp1 + "arm_omega" + Integer.toString(i + 1) + "'=" + Double.toString(a_fast[i]) + "&&";
            tmp2 = tmp2 + "arm_theta" + Integer.toString(i + 1) + "'=" + Double.toString(w_fast[i]) + "&&";
            tmp3 = tmp3 + "arm_omega" + Integer.toString(i + 1) + "'=" + Double.toString((-1) * a_fast[i]) + "&&";
        }
        Location location = product.locations.get(locList.get(0));
        location.clearFlow();
        location.setFlow("arm_theta1'=arm_omega1  && arm_theta2'=arm_omega2 &&  arm_theta3'=arm_omega3 && arm_theta4'=arm_omega4 && arm_theta5'=arm_omega5 && arm_theta6'=arm_omega6&&" + tmp1, product.parameters);
        Transition transition = product.getTransitionBySourceAndTarget(locIndex + 1, locIndex + 2);


        location = product.locations.get(locList.get(1));
        location.clearFlow();
        location.setFlow(tmp2, product.parameters);

        location = product.locations.get(locList.get(2));
        location.clearFlow();
        location.setFlow("arm_theta1'=arm_omega1  && arm_theta2'=arm_omega2 &&  arm_theta3'=arm_omega3 && arm_theta4'=arm_omega4 && arm_theta5'=arm_omega5 && arm_theta6'=arm_omega6&&" + tmp3, product.parameters);


        ArrayList<Double> time = args.get(0);
        time.add(t1);
        time.add(t2);
        time.add(t3);
        args.set(0, time);

    }


    void setForward(double[] t, double lastTime, int locIndex, double[] theta_tar, double[] a_forward, double[] v_forward,ArrayList<Integer> locList) {
        double t1 = t[0] + lastTime;
        double t2 = t[1] + lastTime;
        double t3 = t[2] + lastTime;
        String tmp = "";
        for (int i = 0; i < 6; i++) {
            tmp = tmp + "arm_theta" + Integer.toString(i + 1) + "=" + Double.toString(theta_tar[i]) + " &&";
        }

        Transition transition1 = product.getTransitionBySourceAndTarget(locList.get(3), locList.get(0));
        //todo forward mode is not the first mode
        transition1.setAssignment(tmp, product.parameters);

        String tmp1 = "";
        String tmp2 = "";
        String tmp3 = "";
        for (int i = 0; i < 3; i++) {
            tmp1 = tmp1 + "arm_x" + Integer.toString(i + 1) + "'=arm_v" + Integer.toString(i + 1) + " &&";
            tmp1 = tmp1 + "arm_v" + Integer.toString(i + 1) + "'=" + Double.toString(a_forward[i]) + "&&";

            tmp2 = tmp2 + "arm_x" + Integer.toString(i + 1) + "'=" + Double.toString(v_forward[i]) + "&&";

            tmp3 = tmp3 + "arm_x" + Integer.toString(i + 1) + "'=arm_v" + Integer.toString(i + 1) + " &&";
            tmp3 = tmp3 + "arm_v" + Integer.toString(i + 1) + "'=" + Double.toString(a_forward[i] * (-1)) + "&&";

        }
        Location location = product.locations.get(locList.get(0));
        location.clearFlow();
        location.setFlow(tmp1, product.parameters);
        Transition transition = product.getTransitionBySourceAndTarget(locIndex + 1, locIndex + 2);

        location = product.locations.get(locList.get(1));
        location.clearFlow();
        location.setFlow(tmp2, product.parameters);
        transition = product.getTransitionBySourceAndTarget(locIndex + 2, locIndex + 3);


        location = product.locations.get(locList.get(2));
        location.clearFlow();
        location.setFlow(tmp3, product.parameters);

        ArrayList<Double> time = args.get(0);
        time.add(t1);
        time.add(t2);
        time.add(t3);
        args.set(0, time);
    }

    private boolean notEnd(double step, Integer locIndex) {
        return true;
    }

    public boolean checkInvarientsByODE(ArrayList<ArrayList<Double>> argsList) {
        double step = 0;
        ArrayList<HashMap<String, Double>> allstepMap = new ArrayList<>();
        ArrayList<Integer> locIndexList = new ArrayList<>();
        double max_total = 0;
        for (int n = 0; n < automata_num; n++) {
            HashMap<String, Double> newMap = product.duplicateInitParametersValues();
            allstepMap.add(newMap);
            for (ArrayList<Double> doubles : argsList) {
                double temp = 0;
                for (int j = 0; j < doubles.size(); j++) {
                    temp += doubles.get(j);
                }
                max_total = Math.max(max_total, temp);
            }
            double sum = 0;
            for (int i = 0; i < argsList.get(n).size(); i++) {
                sum += argsList.get(n).get(i);
                argsList.get(n).set(i, sum);
            }
            locIndexList.add(0);
            combination.automata = new ArrayList<>();
            combination.automata.add(product);
        }
        while (step < max_total) {
            for (int n = 0; n < automata_num; n++) {
                int locIndex = locIndexList.get(n);
                HashMap<String, Double> newMap = allstepMap.get(n);
                Automata automata = combination.automata.get(n);
                ArrayList<Double> args = argsList.get(n);
                if (step < args.get(locIndex)) {
                    double before = System.currentTimeMillis();
                    newMap = computeValuesByFlow(newMap, automata.locations.get(path.get(n).get(locIndex)), delta);
                    double after = System.currentTimeMillis();
                    timeAnalyst.addFlowTime((after - before) / 1000);
//                    newMap = computeValuesByFlow(newMap, automata.locations.get(path.get(n).get(locIndex)), delta);

                    before = System.currentTimeMillis();
                    checkConstraints(combination.ca.forbidden, newMap);
                    after = System.currentTimeMillis();

                    timeAnalyst.addForbiddenTime((after - before) / 1000);


                    for (HashMap.Entry<String, Double> entry : newMap.entrySet()) {
                        ctx.set(entry.getKey(), entry.getValue());
                    }
                    //check invariants
                    for (int i = 0; i < automata.locations.get(path.get(n).get(locIndex)).invariants.size(); ++i) {
                        boolean result = (boolean) fel.eval(automata.locations.get(path.get(n).get(locIndex)).invariants.get((i)));
                        if (!result) {
                            String invariant = automata.locations.get(path.get(n).get(locIndex)).invariants.get(i);
                            if (computePenalty(invariant, false) < cerr)
                                continue;
                            if (Double.isNaN(computePenalty(invariant, false))) {
                                sat = false;
                                penalty += 100000;
                                infeasiblelist.get(n).set(locIndex, false);
                            } else {
                                sat = false;
                                //System.out.println(invariant);
                                penalty += computePenalty(invariant, false);
//                                infeasiblelist.get(n).set(locIndex, false);
                            }

                        }
                    }
                    if (step == args.get(locIndex) - 1) {
                        allParametersValuesList.get(n).add((HashMap<String, Double>) newMap.clone());
                        if (locIndex != path.get(n).size() - 1) {
                            locIndex++;

                            Transition transition = automata.getTransitionBySourceAndTarget(path.get(n).get(locIndex - 1), path.get(n).get(locIndex));
                            if (transition == null) {
                                System.out.println("Found no transition");
                                System.exit(-1);
                            }
                            for (HashMap.Entry<String, String> entry : transition.assignments.entrySet()) {
                                Object obj = fel.eval(entry.getValue());
                                double result = 0;
                                if (obj instanceof Integer) result = (int) obj;
                                else if (obj instanceof Double) result = (double) obj;
                                else {
                                    System.out.println("Not Double and Not Integer!");
                                    System.out.println(entry.getValue());
                                    System.exit(0);
                                }
                                newMap.put(entry.getKey(), result);
                            }
                        }
                    }
                    locIndexList.set(n, locIndex);
                    allstepMap.set(n, newMap);
                }
            }
            checkCombine(allstepMap);
            step++;
        }

        return true;
    }

    public boolean checkInvarientsByODEOnebyOne(ArrayList<ArrayList<Double>> argsList) {
        double step = 0;
        ArrayList<HashMap<String, Double>> allstepMap = new ArrayList<>();
        ArrayList<Integer> locIndexList = new ArrayList<>();
        double max_total = 0;
        for (int n = 0; n < automata_num; n++) {
            HashMap<String, Double> newMap = combination.ca.automataList.get(n).duplicateInitParametersValues();
            allstepMap.add(newMap);
            for (ArrayList<Double> doubles : argsList) {
                double temp = 0;
                for (int j = 0; j < doubles.size(); j++) {
                    temp = doubles.get(j);
                }
                max_total = Math.max(max_total, temp);
            }
//            double sum = 0;
//            for (int i = 0; i < argsList.get(n).size(); i++) {
//                sum += argsList.get(n).get(i);
//                argsList.get(n).set(i, sum);
//            }
            locIndexList.add(0);

        }
        while (step < max_total) {
            for (int n = 0; n < automata_num; n++) {
                int locIndex = locIndexList.get(n);
                HashMap<String, Double> newMap = allstepMap.get(n);
                Automata automata = combination.ca.automataList.get(n);
                ArrayList<Double> args = argsList.get(n);
                if (step < args.get(locIndex)) {
                    double before = System.currentTimeMillis();
                    newMap = computeValuesByFlow(newMap, automata.locations.get(path.get(n).get(locIndex)), delta);
                    double after = System.currentTimeMillis();
                    timeAnalyst.addFlowTime((after - before) / 1000);
//                    newMap = computeValuesByFlow(newMap, automata.locations.get(path.get(n).get(locIndex)), delta);

                    before = System.currentTimeMillis();
                    checkConstraints(combination.ca.forbidden, newMap);
                    after = System.currentTimeMillis();

                    timeAnalyst.addForbiddenTime((after - before) / 1000);


                    for (HashMap.Entry<String, Double> entry : newMap.entrySet()) {
                        ctx.set(entry.getKey(), entry.getValue());
                    }
                    //check invariants
                    for (int i = 0; i < automata.locations.get(path.get(n).get(locIndex)).invariants.size(); ++i) {
                        boolean result = (boolean) fel.eval(automata.locations.get(path.get(n).get(locIndex)).invariants.get((i)));
                        if (!result) {
                            String invariant = automata.locations.get(path.get(n).get(locIndex)).invariants.get(i);
                            if (computePenalty(invariant, false) < cerr)
                                continue;
                            if (Double.isNaN(computePenalty(invariant, false))) {
                                sat = false;
                                penalty += 100000;
                                infeasiblelist.get(n).set(locIndex, false);
                            } else {
                                sat = false;
                                //System.out.println(invariant);
                                penalty += computePenalty(invariant, false);
//                                infeasiblelist.get(n).set(locIndex, false);
                            }

                        }
                    }
                    if (step == args.get(locIndex) - 1) {
                        allParametersValuesList.get(n).add((HashMap<String, Double>) newMap.clone());
                        if (locIndex != path.get(n).size() - 1) {
                            locIndex++;

                            Transition transition = automata.getTransitionBySourceAndTarget(path.get(n).get(locIndex - 1), path.get(n).get(locIndex));
                            if (transition == null) {
                                System.out.println("Found no transition");
                                System.exit(-1);
                            }
                            for (HashMap.Entry<String, String> entry : transition.assignments.entrySet()) {
                                Object obj = fel.eval(entry.getValue());
                                double result = 0;
                                if (obj instanceof Integer) result = (int) obj;
                                else if (obj instanceof Double) result = (double) obj;
                                else {
                                    System.out.println("Not Double and Not Integer!");
                                    System.out.println(entry.getValue());
                                    System.exit(0);
                                }
                                newMap.put(entry.getKey(), result);
                            }
                        }
                    }
                    locIndexList.set(n, locIndex);
                    allstepMap.set(n, newMap);
                }
            }
            checkCombine(allstepMap);
            step++;
        }

        return true;
    }


    private double computePenaltyOfConstraint(String expression) {//just one level
        String[] expressions = expression.split("\\|");
        double result = Double.MAX_VALUE;
        for (String string : expressions) {
            if (string.length() <= 0) continue;
            double temp = computePenalty(string, false);
            result = (temp < result) ? temp : result;
        }
        return result;
    }

    private double computePenalty(String expression, boolean isConstraint) {
        if (isConstraint && expression.indexOf("|") != -1)
            return computePenaltyOfConstraint(expression);

        String[] strings;
        String bigPart = "", smallPart = "";
        strings = expression.split("<=|<|>=|>|==");
        Object obj1 = fel.eval(strings[0].trim());
        Object obj2 = fel.eval(strings[1].trim());
        double big = 0, small = 0;
        if (obj1 instanceof Double)
            big = (double) obj1;
        else if (obj1 instanceof Integer) {
            big = (int) obj1;
            //System.out.println(entry.getKey() + " " + entry.getValue());
        } else {
            System.out.println("Not Double and Not Integer!");
            System.out.println(expression);
            System.out.println(obj1);
            System.out.println(obj1.getClass().getName());
            System.out.println("here");
            System.exit(0);
        }
        if (obj2 instanceof Double)
            small = (double) obj2;
        else if (obj2 instanceof Integer) {
            small = (int) obj2;
        } else if (obj2 instanceof Long) {
            small = ((Long) obj2).doubleValue();
        } else {
            small = 0;
            System.out.println("Not Double and Not Integer!");
            System.exit(0);
        }
        return Math.abs(big - small);
    }


    @Override
//    public double getValue(Instance ins) {
//        penalty = 0;
//        globalPenalty = 0;
//        sat = true;
//        allParametersValuesList = new ArrayList<>();
//        infeasiblelist = new ArrayList<>();
//        ArrayList<Integer> pat = PathMap.get((int) ins.getFeature(0));
//        path = new ArrayList<>();
//        path.add(pat);
//
//        for (int i = 0; i < product.rangeParameters.size(); ++i) {
//            product.initParameterValues.put(product.rangeParameters.get(i).name, ins.getFeature(i + 1));
//        }
//        if (combination.ca.staytime4loc) {
//            ArrayList<ArrayList<Double>> args = new ArrayList<>();
//            ArrayList<Double> arg = new ArrayList<>();
//            for (int i = 0; i < pat.size(); ++i)
//                arg.add(ins.getFeature(i + 1 + rangeParaSize));
//            args.add(arg);
//            for (int n = 0; n < automata_num; n++) {
//                ArrayList<HashMap<String, Double>> allParametersValues = new ArrayList<>();
//                allParametersValuesList.add(allParametersValues);
//            }
//
//            double before = System.currentTimeMillis();
//            checkInvarientsByODE(args);
//            double after = System.currentTimeMillis();
//
//            timeAnalyst.addODETime((after - before) / 1000);
//
//        }
//        for (int n = 0; n < automata_num; n++)
//            checkGuards(combination.automata.get(n), n);
//        if (!sat) {
////            System.out.println("guard infesasible!");
//            if (penalty + globalPenalty == 0) {
//                //todo cfg file should have brackets
//                System.out.println("penalty = 0 when unsat");
//                return Double.MAX_VALUE;
//            }
//            double penAll = penalty + globalPenalty;
//            if (penAll < valueArc.penAll) {
//                valueArc.penalty = penalty;
//                valueArc.globalPenalty = globalPenalty;
//                valueArc.penAll = penAll;
//            }
////            System.out.println("path:"+ins.getFeature(0)+"  value:"+penAll);
//            return penAll*100;
//        }
//        double value = 0;
//        for (int n = 0; n < automata_num; n++) {
//            double t = computeValue(n);
//            value += t;
//        }
////        if(value1<0||value2<0){
////            System.out.println("YES");
////        }
////        if(value1*value2>0)
////            return value1+value2;
////        else return value1+value2+10000;
////        System.out.println("path:"+ins.getFeature(0)+"  value:"+value);
//        return value;
//    }

    public double getValue(Instance ins) {

//        ins.setFeature(0, 0.0);

        penalty = 0;
        globalPenalty = 0;
        sat = true;
        allParametersValuesList = new ArrayList<>();
        infeasiblelist = new ArrayList<>();
        ArrayList<Integer> pat = PathMap.get((int) ins.getFeature(0));
        path = new ArrayList<>();
        path.add(pat);

//        for (int i = 0; i < pat.size() - 1; ++i) {
//            System.out.print(product.locations.get(pat.get(i)).name + "->");
//        }
//        System.out.println(product.locations.get(pat.get(pat.size() - 1)).name);
//
//        for (int i = 0; i < pat.size() - 1; ++i) {
//            System.out.print(pat.get(i) + "->");
//        }
//        System.out.println(pat.get(pat.size() - 1));

        int index = 1 + armParaSize * cmdSize;

        for (int i = 0; i < product.rangeParameters.size(); ++i) {
            String param = product.rangeParameters.get(i).name;
            product.initParameterValues.put(param, ins.getFeature(index + i));
            String autName = product.rangeParameters.get(i).name.trim().split("_")[0];
            Automata aut = combination.autMap.get(autName);
            aut.initParameterValues.put(param, ins.getFeature(index + i));
        }

        if (combination.ca.staytime4loc) {

            ArrayList<Double> arg = new ArrayList<>();
            for (int i = 0; i < pat.size(); ++i)
                arg.add(ins.getFeature(i + 1 + rangeParaSize));
            args.add(arg);
            for (int n = 0; n < automata_num; n++) {
                ArrayList<HashMap<String, Double>> allParametersValues = new ArrayList<>();
                allParametersValuesList.add(allParametersValues);
            }

            double before = System.currentTimeMillis();
            checkInvarientsByODE(args);
            double after = System.currentTimeMillis();

            timeAnalyst.addODETime((after - before) / 1000);

        } else {

            ArrayList<Double> arg = new ArrayList<>();
            arg.add(delta);
            args.add(arg);

            for (int n = 0; n < automata_num; n++) {
                ArrayList<HashMap<String, Double>> allParametersValues = new ArrayList<>();
                allParametersValuesList.add(allParametersValues);
            }

            actualCmdSize = countCmd(pat);
            double before = System.currentTimeMillis();
            checkInvarientsByODEForArmBelt(args, ins);
            double after = System.currentTimeMillis();

            timeAnalyst.addODETime((after - before) / 1000);
        }
//        for (int n = 0; n < automata_num; n++)
//            checkGuards(combination.automata.get(n), n);
        if (!sat) {
//            System.out.println("guard infesasible!");
            if (penalty + globalPenalty == 0) {
                //todo cfg file should have brackets
                System.out.println("penalty = 0 when unsat");
                return Double.MAX_VALUE;
            }
            double penAll = penalty + globalPenalty;
            if (penAll < valueArc.penAll) {
                valueArc.penalty = penalty;
                valueArc.globalPenalty = globalPenalty;
                valueArc.penAll = penAll;
            }
//            System.out.println("path:"+ins.getFeature(0)+"  value:"+penAll);
            return penAll * 100;
        }

        double value = computeValue(args.get(0));

//        if(value1<0||value2<0){
//            System.out.println("YES");
//        }
//        if(value1*value2>0)
//            return value1+value2;
//        else return value1+value2+10000;
//        System.out.println("path:"+ins.getFeature(0)+"  value:"+value);
        return value;
    }

    private int countCmd(ArrayList<Integer> path) {
        Set<String> cmdSet = new HashSet<>();
        cmdSet.add("fp1");
        cmdSet.add("lp1");
        cmdSet.add("jp1");

        int cnt = 0;
        for (Integer integer : path) {
            String armLocName = product.locations.get(integer).name.split(",")[0];
            if (cmdSet.contains(armLocName)) cnt++;
        }

        return cnt;
    }

    private void setAutomataByins(Instance ins) {
    }


    public double computeValue(ArrayList<Double> arg) {
        return arg.get(1+actualCmdSize*3) + prepareTime -10000;
    }

    @Override
    public Dimension getDim() {
        return dim;
    }

    public double[] getTime() {
        return time;
    }

    @Override
    public ArrayList<Boolean> getInfeasibleLoc(int index) {
        return infeasiblelist.get(index);
    }
}
