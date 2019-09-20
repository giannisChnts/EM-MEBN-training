

import java.io.Serializable;

public class QueryResultSummary implements Serializable {
	
	private int shipID = -1;
	private String output;
	private RandomVariableInfo shipOfInterestInfo;
	private RandomVariableInfo bombPortPlan;
	private RandomVariableInfo exchangeIllicitCargoPlan;
	private RandomVariableInfo hijacked;
	private RandomVariableInfo terroristCrew;
	private RandomVariableInfo[] terroristPersonInfo;
	
	public String getOutput() {
		return output;
	}
	public void setOutput(String output) {
		this.output = output;
	}
	public RandomVariableInfo getShipOfInterestInfo() {
		return shipOfInterestInfo;
	}
	public void setShipOfInterestInfo(RandomVariableInfo shipOfInterestInfo) {
		this.shipOfInterestInfo = shipOfInterestInfo;
	}
	public RandomVariableInfo getHijacked() {
		return hijacked;
	}
	public void setHijacked(RandomVariableInfo hijacked) {
		this.hijacked = hijacked;
	}
	public RandomVariableInfo getTerroristCrew() {
		return terroristCrew;
	}
	public void setTerroristCrew(RandomVariableInfo terroristCrew) {
		this.terroristCrew = terroristCrew;
	}
	public RandomVariableInfo[] getTerroristPersonInfo() {
		return terroristPersonInfo;
	}
	public void setTerroristPersonInfo(RandomVariableInfo[] terroristPersonInfo) {
		this.terroristPersonInfo = terroristPersonInfo;
	}
	public RandomVariableInfo getBombPortPlan() {
		return bombPortPlan;
	}
	public void setBombPortPlan(RandomVariableInfo bombPortPlan) {
		this.bombPortPlan = bombPortPlan;
	}
	public RandomVariableInfo getExchangeIllicitCargoPlan() {
		return exchangeIllicitCargoPlan;
	}
	public void setExchangeIllicitCargoPlan(
			RandomVariableInfo exchangeIllicitCargoPlan) {
		this.exchangeIllicitCargoPlan = exchangeIllicitCargoPlan;
	}
	/**
	 * @return the shipID
	 */
	public int getShipID() {
		return shipID;
	}
	/**
	 * @param shipID the shipID to set
	 */
	public void setShipID(int shipID) {
		this.shipID = shipID;
	}
	
	

}